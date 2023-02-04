// SPDX-License-Identifier: GPL-2.0
/*
 * fs/f2fs/data.c
 *
 * Copyright (c) 2012 Samsung Electronics Co., Ltd.
 *             http://www.samsung.com/
 */
#include <linux/fs.h>
#include <linux/f2fs_fs.h>
#include <linux/buffer_head.h>
#include <linux/mpage.h>
#include <linux/writeback.h>
#include <linux/backing-dev.h>
#include <linux/pagevec.h>
#include <linux/blkdev.h>
#include <linux/bio.h>
#include <linux/swap.h>
#include <linux/prefetch.h>
#include <linux/uio.h>
#include <linux/cleancache.h>
#include <linux/sched/signal.h>
#ifdef F2FS_DELTA_COMPRESS
#include <linux/lzo.h>//revised
#include <linux/pagemap.h>
#include <linux/time.h>
#include <string.h>
#ifdef F2FS_MAIN_COMPRESS
#include <linux/fs_struct.h>
#endif
#endif
#include "f2fs.h"
#include "node.h"
#include "segment.h"
#include "trace.h"
#include <trace/events/f2fs.h>
#include <trace/events/android_fs.h>

#define NUM_PREALLOC_POST_READ_CTXS	128

static struct kmem_cache *bio_post_read_ctx_cache;
static struct kmem_cache *bio_entry_slab;
static mempool_t *bio_post_read_ctx_pool;
static struct bio_set f2fs_bioset;

#define	F2FS_BIO_POOL_SIZE	NR_CURSEG_TYPE

int __init f2fs_init_bioset(void)
{
	if (bioset_init(&f2fs_bioset, F2FS_BIO_POOL_SIZE,
					0, BIOSET_NEED_BVECS))
		return -ENOMEM;
	return 0;
}

void f2fs_destroy_bioset(void)
{
	bioset_exit(&f2fs_bioset);
}

static inline struct bio *__f2fs_bio_alloc(gfp_t gfp_mask,
						unsigned int nr_iovecs)
{
	return bio_alloc_bioset(gfp_mask, nr_iovecs, &f2fs_bioset);
}

struct bio *f2fs_bio_alloc(struct f2fs_sb_info *sbi, int npages, bool no_fail)
{
	struct bio *bio;

	if (no_fail) {
		/* No failure on bio allocation */
		bio = __f2fs_bio_alloc(GFP_NOIO, npages);
		if (!bio)
			bio = __f2fs_bio_alloc(GFP_NOIO | __GFP_NOFAIL, npages);
		return bio;
	}
	if (time_to_inject(sbi, FAULT_ALLOC_BIO)) {
		f2fs_show_injection_info(sbi, FAULT_ALLOC_BIO);
		return NULL;
	}

	return __f2fs_bio_alloc(GFP_KERNEL, npages);
}

static bool __is_cp_guaranteed(struct page *page)
{
	struct address_space *mapping = page->mapping;
	struct inode *inode;
	struct f2fs_sb_info *sbi;

	if (!mapping)
		return false;

	if (f2fs_is_compressed_page(page))
		return false;

	inode = mapping->host;
	sbi = F2FS_I_SB(inode);

	if (inode->i_ino == F2FS_META_INO(sbi) ||
			inode->i_ino ==  F2FS_NODE_INO(sbi) ||
			S_ISDIR(inode->i_mode) ||
			(S_ISREG(inode->i_mode) &&
			(f2fs_is_atomic_file(inode) || IS_NOQUOTA(inode))) ||
			is_cold_data(page))
		return true;
	return false;
}

static enum count_type __read_io_type(struct page *page)
{
	struct address_space *mapping = page_file_mapping(page);

	if (mapping) {
		struct inode *inode = mapping->host;
		struct f2fs_sb_info *sbi = F2FS_I_SB(inode);

		if (inode->i_ino == F2FS_META_INO(sbi))
			return F2FS_RD_META;

		if (inode->i_ino == F2FS_NODE_INO(sbi))
			return F2FS_RD_NODE;
	}
	return F2FS_RD_DATA;
}

/* postprocessing steps for read bios */
enum bio_post_read_step {
	STEP_DECRYPT,
	STEP_DECOMPRESS,
	STEP_VERITY,
};

struct bio_post_read_ctx {
	struct bio *bio;
	struct f2fs_sb_info *sbi;
	struct work_struct work;
	unsigned int enabled_steps;
};

static void __read_end_io(struct bio *bio, bool compr, bool verity)
{
	struct page *page;
	struct bio_vec *bv;
	int i;

	bio_for_each_segment_all(bv, bio, i) {
		page = bv->bv_page;

#ifdef CONFIG_F2FS_FS_COMPRESSION
		if (compr && f2fs_is_compressed_page(page)) {
			f2fs_decompress_pages(bio, page, verity);
			continue;
		}
#endif

		/* PG_error was set if any post_read step failed */
		if (bio->bi_status || PageError(page)) {
			ClearPageUptodate(page);
			/* will re-read again later */
			ClearPageError(page);
		} else {
			SetPageUptodate(page);
		}
		dec_page_count(F2FS_P_SB(page), __read_io_type(page));
		unlock_page(page);
	}
}

static void f2fs_release_read_bio(struct bio *bio);
static void __f2fs_read_end_io(struct bio *bio, bool compr, bool verity)
{
	if (!compr)
		__read_end_io(bio, false, verity);
	f2fs_release_read_bio(bio);
}

static void f2fs_decompress_bio(struct bio *bio, bool verity)
{
	__read_end_io(bio, true, verity);
}

static void bio_post_read_processing(struct bio_post_read_ctx *ctx);

static void f2fs_decrypt_work(struct bio_post_read_ctx *ctx)
{
	fscrypt_decrypt_bio(ctx->bio);
}

static void f2fs_decompress_work(struct bio_post_read_ctx *ctx)
{
	f2fs_decompress_bio(ctx->bio, ctx->enabled_steps & (1 << STEP_VERITY));
}

#ifdef CONFIG_F2FS_FS_COMPRESSION
static void f2fs_verify_pages(struct page **rpages, unsigned int cluster_size)
{
	f2fs_decompress_end_io(rpages, cluster_size, false, true);
}

static void f2fs_verify_bio(struct bio *bio)
{
	struct page *page = bio_first_page_all(bio);
	struct decompress_io_ctx *dic =
			(struct decompress_io_ctx *)page_private(page);

	f2fs_verify_pages(dic->rpages, dic->cluster_size);
	f2fs_free_dic(dic);
}
#endif

static void f2fs_verity_work(struct work_struct *work)
{
	struct bio_post_read_ctx *ctx =
		container_of(work, struct bio_post_read_ctx, work);
	struct bio *bio = ctx->bio;
#ifdef CONFIG_F2FS_FS_COMPRESSION
	unsigned int enabled_steps = ctx->enabled_steps;
#endif

	/*
	 * fsverity_verify_bio() may call readpages() again, and while verity
	 * will be disabled for this, decryption may still be needed, resulting
	 * in another bio_post_read_ctx being allocated.  So to prevent
	 * deadlocks we need to release the current ctx to the mempool first.
	 * This assumes that verity is the last post-read step.
	 */
	mempool_free(ctx, bio_post_read_ctx_pool);
	bio->bi_private = NULL;

#ifdef CONFIG_F2FS_FS_COMPRESSION
	/* previous step is decompression */
	if (enabled_steps & (1 << STEP_DECOMPRESS)) {
		f2fs_verify_bio(bio);
		f2fs_release_read_bio(bio);
		return;
	}
#endif

	fsverity_verify_bio(bio);
	__f2fs_read_end_io(bio, false, false);
}

static void f2fs_post_read_work(struct work_struct *work)
{
	struct bio_post_read_ctx *ctx =
		container_of(work, struct bio_post_read_ctx, work);

	if (ctx->enabled_steps & (1 << STEP_DECRYPT))
		f2fs_decrypt_work(ctx);

	if (ctx->enabled_steps & (1 << STEP_DECOMPRESS))
		f2fs_decompress_work(ctx);

	if (ctx->enabled_steps & (1 << STEP_VERITY)) {
		INIT_WORK(&ctx->work, f2fs_verity_work);
		fsverity_enqueue_verify_work(&ctx->work);
		return;
	}

	__f2fs_read_end_io(ctx->bio,
		ctx->enabled_steps & (1 << STEP_DECOMPRESS), false);
}

static void f2fs_enqueue_post_read_work(struct f2fs_sb_info *sbi,
						struct work_struct *work)
{
	queue_work(sbi->post_read_wq, work);
}

static void bio_post_read_processing(struct bio_post_read_ctx *ctx)
{
	/*
	 * We use different work queues for decryption and for verity because
	 * verity may require reading metadata pages that need decryption, and
	 * we shouldn't recurse to the same workqueue.
	 */

	if (ctx->enabled_steps & (1 << STEP_DECRYPT) ||
		ctx->enabled_steps & (1 << STEP_DECOMPRESS)) {
		INIT_WORK(&ctx->work, f2fs_post_read_work);
		f2fs_enqueue_post_read_work(ctx->sbi, &ctx->work);
		return;
	}

	if (ctx->enabled_steps & (1 << STEP_VERITY)) {
		INIT_WORK(&ctx->work, f2fs_verity_work);
		fsverity_enqueue_verify_work(&ctx->work);
		return;
	}

	__f2fs_read_end_io(ctx->bio, false, false);
}

static bool f2fs_bio_post_read_required(struct bio *bio)
{
	return bio->bi_private;
}

static void f2fs_read_end_io(struct bio *bio)
{
	struct page *first_page = bio->bi_io_vec[0].bv_page;
	struct f2fs_sb_info *sbi = F2FS_P_SB(first_page);

	if (time_to_inject(sbi, FAULT_READ_IO)) {
		f2fs_show_injection_info(sbi, FAULT_READ_IO);
		bio->bi_status = BLK_STS_IOERR;
	}

	if (f2fs_bio_post_read_required(bio)) {
		struct bio_post_read_ctx *ctx = bio->bi_private;

		bio_post_read_processing(ctx);
		return;
	}

	if (first_page != NULL &&
		__read_io_type(first_page) == F2FS_RD_DATA) {
		trace_android_fs_dataread_end(first_page->mapping->host,
						page_offset(first_page),
						bio->bi_iter.bi_size);
	}

	__f2fs_read_end_io(bio, false, false);
}

static void f2fs_write_end_io(struct bio *bio)
{
	struct f2fs_sb_info *sbi = bio->bi_private;
	struct bio_vec *bvec;
	int i;

	if (time_to_inject(sbi, FAULT_WRITE_IO)) {
		f2fs_show_injection_info(sbi, FAULT_WRITE_IO);
		bio->bi_status = BLK_STS_IOERR;
	}

	bio_for_each_segment_all(bvec, bio, i) {
		struct page *page = bvec->bv_page;
		enum count_type type = WB_DATA_TYPE(page);

		if (IS_DUMMY_WRITTEN_PAGE(page)) {
			set_page_private(page, (unsigned long)NULL);
			ClearPagePrivate(page);
			unlock_page(page);
			mempool_free(page, sbi->write_io_dummy);

			if (unlikely(bio->bi_status))
				f2fs_stop_checkpoint(sbi, true);
			continue;
		}

		fscrypt_finalize_bounce_page(&page);

#ifdef CONFIG_F2FS_FS_COMPRESSION
		if (f2fs_is_compressed_page(page)) {
			f2fs_compress_write_end_io(bio, page);
			continue;
		}
#endif

		if (unlikely(bio->bi_status)) {
			mapping_set_error(page->mapping, -EIO);
			if (type == F2FS_WB_CP_DATA)
				f2fs_stop_checkpoint(sbi, true);
		}

		f2fs_bug_on(sbi, page->mapping == NODE_MAPPING(sbi) &&
					page->index != nid_of_node(page));

		dec_page_count(sbi, type);
		if (f2fs_in_warm_node_list(sbi, page))
			f2fs_del_fsync_node_entry(sbi, page);
		clear_cold_data(page);
		end_page_writeback(page);
	}
	if (!get_pages(sbi, F2FS_WB_CP_DATA) &&
				wq_has_sleeper(&sbi->cp_wait))
		wake_up(&sbi->cp_wait);

	bio_put(bio);
}

/*
 * Return true, if pre_bio's bdev is same as its target device.
 */
struct block_device *f2fs_target_device(struct f2fs_sb_info *sbi,
				block_t blk_addr, struct bio *bio)
{
	struct block_device *bdev = sbi->sb->s_bdev;
	int i;

	if (f2fs_is_multi_device(sbi)) {
		for (i = 0; i < sbi->s_ndevs; i++) {
			if (FDEV(i).start_blk <= blk_addr &&
			    FDEV(i).end_blk >= blk_addr) {
				blk_addr -= FDEV(i).start_blk;
				bdev = FDEV(i).bdev;
				break;
			}
		}
	}
	if (bio) {
		bio_set_dev(bio, bdev);
		bio->bi_iter.bi_sector = SECTOR_FROM_BLOCK(blk_addr);
	}
	return bdev;
}

int f2fs_target_device_index(struct f2fs_sb_info *sbi, block_t blkaddr)
{
	int i;

	if (!f2fs_is_multi_device(sbi))
		return 0;

	for (i = 0; i < sbi->s_ndevs; i++)
		if (FDEV(i).start_blk <= blkaddr && FDEV(i).end_blk >= blkaddr)
			return i;
	return 0;
}

static bool __same_bdev(struct f2fs_sb_info *sbi,
				block_t blk_addr, struct bio *bio)
{
	struct block_device *b = f2fs_target_device(sbi, blk_addr, NULL);
	return bio->bi_disk == b->bd_disk && bio->bi_partno == b->bd_partno;
}

/*
 * Low-level block read/write IO operations.
 */
static struct bio *__bio_alloc(struct f2fs_io_info *fio, int npages)
{
	struct f2fs_sb_info *sbi = fio->sbi;
	struct bio *bio;

	bio = f2fs_bio_alloc(sbi, npages, true);

	f2fs_target_device(sbi, fio->new_blkaddr, bio);
	if (is_read_io(fio->op)) {
		bio->bi_end_io = f2fs_read_end_io;
		bio->bi_private = NULL;
	} else {
		bio->bi_end_io = f2fs_write_end_io;
		bio->bi_private = sbi;
		bio->bi_write_hint = f2fs_io_type_to_rw_hint(sbi,
						fio->type, fio->temp);
	}
	if (fio->io_wbc)
		wbc_init_bio(fio->io_wbc, bio);

	return bio;
}

static void f2fs_set_bio_crypt_ctx(struct bio *bio, const struct inode *inode,
				  pgoff_t first_idx,
				  const struct f2fs_io_info *fio,
				  gfp_t gfp_mask)
{
	/*
	 * The f2fs garbage collector sets ->encrypted_page when it wants to
	 * read/write raw data without encryption.
	 */
	if (!fio || !fio->encrypted_page)
		fscrypt_set_bio_crypt_ctx(bio, inode, first_idx, gfp_mask);
	else if (fscrypt_inode_should_skip_dm_default_key(inode))
		bio_set_skip_dm_default_key(bio);
}

static bool f2fs_crypt_mergeable_bio(struct bio *bio, const struct inode *inode,
				     pgoff_t next_idx,
				     const struct f2fs_io_info *fio)
{
	/*
	 * The f2fs garbage collector sets ->encrypted_page when it wants to
	 * read/write raw data without encryption.
	 */
	if (fio && fio->encrypted_page)
		return !bio_has_crypt_ctx(bio) &&
			(bio_should_skip_dm_default_key(bio) ==
			 fscrypt_inode_should_skip_dm_default_key(inode));

	return fscrypt_mergeable_bio(bio, inode, next_idx);
}

static inline void __submit_bio(struct f2fs_sb_info *sbi,
				struct bio *bio, enum page_type type)
{
	if (!is_read_io(bio_op(bio))) {
		unsigned int start;

		if (type != DATA && type != NODE)
			goto submit_io;

		if (test_opt(sbi, LFS) && current->plug)
			blk_finish_plug(current->plug);

		if (F2FS_IO_ALIGNED(sbi))
			goto submit_io;

		start = bio->bi_iter.bi_size >> F2FS_BLKSIZE_BITS;
		start %= F2FS_IO_SIZE(sbi);

		if (start == 0)
			goto submit_io;

		/* fill dummy pages */
		for (; start < F2FS_IO_SIZE(sbi); start++) {
			struct page *page =
				mempool_alloc(sbi->write_io_dummy,
					      GFP_NOIO | __GFP_NOFAIL);
			f2fs_bug_on(sbi, !page);

			zero_user_segment(page, 0, PAGE_SIZE);
			SetPagePrivate(page);
			set_page_private(page, (unsigned long)DUMMY_WRITTEN_PAGE);
			lock_page(page);
			if (bio_add_page(bio, page, PAGE_SIZE, 0) < PAGE_SIZE)
				f2fs_bug_on(sbi, 1);
		}
		/*
		 * In the NODE case, we lose next block address chain. So, we
		 * need to do checkpoint in f2fs_sync_file.
		 */
		if (type == NODE)
			set_sbi_flag(sbi, SBI_NEED_CP);
	}
submit_io:
	if (is_read_io(bio_op(bio)))
		trace_f2fs_submit_read_bio(sbi->sb, type, bio);
	else
		trace_f2fs_submit_write_bio(sbi->sb, type, bio);
	submit_bio(bio);
}

static void __f2fs_submit_read_bio(struct f2fs_sb_info *sbi,
				struct bio *bio, enum page_type type)
{
	if (trace_android_fs_dataread_start_enabled() && (type == DATA)) {
		struct page *first_page = bio->bi_io_vec[0].bv_page;

		if (first_page != NULL &&
			__read_io_type(first_page) == F2FS_RD_DATA) {
			char *path, pathbuf[MAX_TRACE_PATHBUF_LEN];

			path = android_fstrace_get_pathname(pathbuf,
						MAX_TRACE_PATHBUF_LEN,
						first_page->mapping->host);

			trace_android_fs_dataread_start(
				first_page->mapping->host,
				page_offset(first_page),
				bio->bi_iter.bi_size,
				current->pid,
				path,
				current->comm);
		}
	}
	__submit_bio(sbi, bio, type);
}

void f2fs_submit_bio(struct f2fs_sb_info *sbi,
				struct bio *bio, enum page_type type)
{
	__submit_bio(sbi, bio, type);
}

static void __submit_merged_bio(struct f2fs_bio_info *io)
{
	struct f2fs_io_info *fio = &io->fio;

	if (!io->bio)
		return;

	bio_set_op_attrs(io->bio, fio->op, fio->op_flags);

	if (is_read_io(fio->op))
		trace_f2fs_prepare_read_bio(io->sbi->sb, fio->type, io->bio);
	else
		trace_f2fs_prepare_write_bio(io->sbi->sb, fio->type, io->bio);

	__submit_bio(io->sbi, io->bio, fio->type);
	io->bio = NULL;
}

static bool __has_merged_page(struct bio *bio, struct inode *inode,
						struct page *page, nid_t ino)
{
	struct bio_vec *bvec;
	int i;

	if (!bio)
		return false;

	if (!inode && !page && !ino)
		return true;

	bio_for_each_segment_all(bvec, bio, i) {
		struct page *target = bvec->bv_page;

		if (fscrypt_is_bounce_page(target)) {
			target = fscrypt_pagecache_page(target);
			if (IS_ERR(target))
				continue;
		}
		if (f2fs_is_compressed_page(target)) {
			target = f2fs_compress_control_page(target);
			if (IS_ERR(target))
				continue;
		}

		if (inode && inode == target->mapping->host)
			return true;
		if (page && page == target)
			return true;
		if (ino && ino == ino_of_node(target))
			return true;
	}

	return false;
}

static void __f2fs_submit_merged_write(struct f2fs_sb_info *sbi,
				enum page_type type, enum temp_type temp)
{
	enum page_type btype = PAGE_TYPE_OF_BIO(type);
	struct f2fs_bio_info *io = sbi->write_io[btype] + temp;

	down_write(&io->io_rwsem);

	/* change META to META_FLUSH in the checkpoint procedure */
	if (type >= META_FLUSH) {
		io->fio.type = META_FLUSH;
		io->fio.op = REQ_OP_WRITE;
		io->fio.op_flags = REQ_META | REQ_PRIO | REQ_SYNC;
		if (!test_opt(sbi, NOBARRIER))
			io->fio.op_flags |= REQ_PREFLUSH | REQ_FUA;
	}
	__submit_merged_bio(io);
	up_write(&io->io_rwsem);
}

static void __submit_merged_write_cond(struct f2fs_sb_info *sbi,
				struct inode *inode, struct page *page,
				nid_t ino, enum page_type type, bool force)
{
	enum temp_type temp;
	bool ret = true;

	for (temp = HOT; temp < NR_TEMP_TYPE; temp++) {
		if (!force)	{
			enum page_type btype = PAGE_TYPE_OF_BIO(type);
			struct f2fs_bio_info *io = sbi->write_io[btype] + temp;

			down_read(&io->io_rwsem);
			ret = __has_merged_page(io->bio, inode, page, ino);
			up_read(&io->io_rwsem);
		}
		if (ret)
			__f2fs_submit_merged_write(sbi, type, temp);

		/* TODO: use HOT temp only for meta pages now. */
		if (type >= META)
			break;
	}
}

void f2fs_submit_merged_write(struct f2fs_sb_info *sbi, enum page_type type)
{
	__submit_merged_write_cond(sbi, NULL, NULL, 0, type, true);
}

void f2fs_submit_merged_write_cond(struct f2fs_sb_info *sbi,
				struct inode *inode, struct page *page,
				nid_t ino, enum page_type type)
{
	__submit_merged_write_cond(sbi, inode, page, ino, type, false);
}

void f2fs_flush_merged_writes(struct f2fs_sb_info *sbi)
{
	f2fs_submit_merged_write(sbi, DATA);
	f2fs_submit_merged_write(sbi, NODE);
	f2fs_submit_merged_write(sbi, META);
}

/*
 * Fill the locked page with data located in the block address.
 * A caller needs to unlock the page on failure.
 */
int f2fs_submit_page_bio(struct f2fs_io_info *fio)
{
	struct bio *bio;
	struct page *page = fio->encrypted_page ?
			fio->encrypted_page : fio->page;

	if (!f2fs_is_valid_blkaddr(fio->sbi, fio->new_blkaddr,
			fio->is_por ? META_POR : (__is_meta_io(fio) ?
			META_GENERIC : DATA_GENERIC_ENHANCE)))
		return -EFSCORRUPTED;

	trace_f2fs_submit_page_bio(page, fio);
	f2fs_trace_ios(fio, 0);

	/* Allocate a new bio */
	bio = __bio_alloc(fio, 1);

	f2fs_set_bio_crypt_ctx(bio, fio->page->mapping->host,
			       fio->page->index, fio, GFP_NOIO);

	if (bio_add_page(bio, page, PAGE_SIZE, 0) < PAGE_SIZE) {
		bio_put(bio);
		return -EFAULT;
	}

	if (fio->io_wbc && !is_read_io(fio->op))
		wbc_account_io(fio->io_wbc, page, PAGE_SIZE);

	bio_set_op_attrs(bio, fio->op, fio->op_flags);

	inc_page_count(fio->sbi, is_read_io(fio->op) ?
			__read_io_type(page): WB_DATA_TYPE(fio->page));

	if (is_read_io(fio->op))
		__f2fs_submit_read_bio(fio->sbi, bio, fio->type);
	else
		__submit_bio(fio->sbi, bio, fio->type);
	return 0;
}

static bool page_is_mergeable(struct f2fs_sb_info *sbi, struct bio *bio,
				block_t last_blkaddr, block_t cur_blkaddr)
{
	if (last_blkaddr + 1 != cur_blkaddr)
		return false;
	return __same_bdev(sbi, cur_blkaddr, bio);
}

static bool io_type_is_mergeable(struct f2fs_bio_info *io,
						struct f2fs_io_info *fio)
{
	if (io->fio.op != fio->op)
		return false;
	return io->fio.op_flags == fio->op_flags;
}

static bool io_is_mergeable(struct f2fs_sb_info *sbi, struct bio *bio,
					struct f2fs_bio_info *io,
					struct f2fs_io_info *fio,
					block_t last_blkaddr,
					block_t cur_blkaddr)
{
	if (F2FS_IO_ALIGNED(sbi) && (fio->type == DATA || fio->type == NODE)) {
		unsigned int filled_blocks =
				F2FS_BYTES_TO_BLK(bio->bi_iter.bi_size);
		unsigned int io_size = F2FS_IO_SIZE(sbi);
		unsigned int left_vecs = bio->bi_max_vecs - bio->bi_vcnt;

		/* IOs in bio is aligned and left space of vectors is not enough */
		if (!(filled_blocks % io_size) && left_vecs < io_size)
			return false;
	}
	if (!page_is_mergeable(sbi, bio, last_blkaddr, cur_blkaddr))
		return false;
	return io_type_is_mergeable(io, fio);
}

static void add_bio_entry(struct f2fs_sb_info *sbi, struct bio *bio,
				struct page *page, enum temp_type temp)
{
	struct f2fs_bio_info *io = sbi->write_io[DATA] + temp;
	struct bio_entry *be;

	be = f2fs_kmem_cache_alloc(bio_entry_slab, GFP_NOFS);
	be->bio = bio;
	bio_get(bio);

	if (bio_add_page(bio, page, PAGE_SIZE, 0) != PAGE_SIZE)
		f2fs_bug_on(sbi, 1);

	down_write(&io->bio_list_lock);
	list_add_tail(&be->list, &io->bio_list);
	up_write(&io->bio_list_lock);
}

static void del_bio_entry(struct bio_entry *be)
{
	list_del(&be->list);
	kmem_cache_free(bio_entry_slab, be);
}

static int add_ipu_page(struct f2fs_io_info *fio, struct bio **bio,
							struct page *page)
{
	struct f2fs_sb_info *sbi = fio->sbi;
	enum temp_type temp;
	bool found = false;
	int ret = -EAGAIN;

	for (temp = HOT; temp < NR_TEMP_TYPE && !found; temp++) {
		struct f2fs_bio_info *io = sbi->write_io[DATA] + temp;
		struct list_head *head = &io->bio_list;
		struct bio_entry *be;

		down_write(&io->bio_list_lock);
		list_for_each_entry(be, head, list) {
			if (be->bio != *bio)
				continue;

			found = true;

			f2fs_bug_on(sbi, !page_is_mergeable(sbi, *bio,
							    *fio->last_block,
							    fio->new_blkaddr));
			if (f2fs_crypt_mergeable_bio(*bio,
					fio->page->mapping->host,
					fio->page->index, fio) &&
			    bio_add_page(*bio, page, PAGE_SIZE, 0) ==
					PAGE_SIZE) {
				ret = 0;
				break;
			}

			/* page can't be merged into bio; submit the bio */
			del_bio_entry(be);
			__submit_bio(sbi, *bio, DATA);
			break;
		}
		up_write(&io->bio_list_lock);
	}

	if (ret) {
		bio_put(*bio);
		*bio = NULL;
	}

	return ret;
}

void f2fs_submit_merged_ipu_write(struct f2fs_sb_info *sbi,
					struct bio **bio, struct page *page)
{
	enum temp_type temp;
	bool found = false;
	struct bio *target = bio ? *bio : NULL;

	for (temp = HOT; temp < NR_TEMP_TYPE && !found; temp++) {
		struct f2fs_bio_info *io = sbi->write_io[DATA] + temp;
		struct list_head *head = &io->bio_list;
		struct bio_entry *be;

		if (list_empty(head))
			continue;

		down_read(&io->bio_list_lock);
		list_for_each_entry(be, head, list) {
			if (target)
				found = (target == be->bio);
			else
				found = __has_merged_page(be->bio, NULL,
								page, 0);
			if (found)
				break;
		}
		up_read(&io->bio_list_lock);

		if (!found)
			continue;

		found = false;

		down_write(&io->bio_list_lock);
		list_for_each_entry(be, head, list) {
			if (target)
				found = (target == be->bio);
			else
				found = __has_merged_page(be->bio, NULL,
								page, 0);
			if (found) {
				target = be->bio;
				del_bio_entry(be);
				break;
			}
		}
		up_write(&io->bio_list_lock);
	}

	if (found)
		__submit_bio(sbi, target, DATA);
	if (bio && *bio) {
		bio_put(*bio);
		*bio = NULL;
	}
}

int f2fs_merge_page_bio(struct f2fs_io_info *fio)
{
	struct bio *bio = *fio->bio;
	struct page *page = fio->encrypted_page ?
			fio->encrypted_page : fio->page;

	if (!f2fs_is_valid_blkaddr(fio->sbi, fio->new_blkaddr,
			__is_meta_io(fio) ? META_GENERIC : DATA_GENERIC))
		return -EFSCORRUPTED;

	trace_f2fs_submit_page_bio(page, fio);
	f2fs_trace_ios(fio, 0);

	if (bio && !page_is_mergeable(fio->sbi, bio, *fio->last_block,
				       fio->new_blkaddr))
		f2fs_submit_merged_ipu_write(fio->sbi, &bio, NULL);

alloc_new:
	if (!bio) {
		bio = __bio_alloc(fio, BIO_MAX_PAGES);
		f2fs_set_bio_crypt_ctx(bio, fio->page->mapping->host,
				       fio->page->index, fio,
				       GFP_NOIO);
		bio_set_op_attrs(bio, fio->op, fio->op_flags);

		add_bio_entry(fio->sbi, bio, page, fio->temp);
	} else {
		if (add_ipu_page(fio, &bio, page))
			goto alloc_new;
	}

	if (fio->io_wbc)
		wbc_account_io(fio->io_wbc, page, PAGE_SIZE);

	inc_page_count(fio->sbi, WB_DATA_TYPE(page));

	*fio->last_block = fio->new_blkaddr;
	*fio->bio = bio;

	return 0;
}

void f2fs_submit_page_write(struct f2fs_io_info *fio)
{
	struct f2fs_sb_info *sbi = fio->sbi;
	enum page_type btype = PAGE_TYPE_OF_BIO(fio->type);
	struct f2fs_bio_info *io = sbi->write_io[btype] + fio->temp;
	struct page *bio_page;

	f2fs_bug_on(sbi, is_read_io(fio->op));

	down_write(&io->io_rwsem);
next:
	if (fio->in_list) {
		spin_lock(&io->io_lock);
		if (list_empty(&io->io_list)) {
			spin_unlock(&io->io_lock);
			goto out;
		}
		fio = list_first_entry(&io->io_list,
						struct f2fs_io_info, list);
		list_del(&fio->list);
		spin_unlock(&io->io_lock);
	}

	verify_fio_blkaddr(fio);

	if (fio->encrypted_page)
		bio_page = fio->encrypted_page;
	else if (fio->compressed_page)
		bio_page = fio->compressed_page;
	else
		bio_page = fio->page;

	/* set submitted = true as a return value */
	fio->submitted = true;

	inc_page_count(sbi, WB_DATA_TYPE(bio_page));

	if (io->bio &&
	    (!io_is_mergeable(sbi, io->bio, io, fio, io->last_block_in_bio,
			      fio->new_blkaddr) ||
	     !f2fs_crypt_mergeable_bio(io->bio, fio->page->mapping->host,
				       fio->page->index, fio)))
		__submit_merged_bio(io);
alloc_new:
	if (io->bio == NULL) {
		if (F2FS_IO_ALIGNED(sbi) &&
				(fio->type == DATA || fio->type == NODE) &&
				fio->new_blkaddr & F2FS_IO_SIZE_MASK(sbi)) {
			dec_page_count(sbi, WB_DATA_TYPE(bio_page));
			fio->retry = true;
			goto skip;
		}
		io->bio = __bio_alloc(fio, BIO_MAX_PAGES);
		f2fs_set_bio_crypt_ctx(io->bio, fio->page->mapping->host,
				       fio->page->index, fio,
				       GFP_NOIO);
		io->fio = *fio;
	}

	if (bio_add_page(io->bio, bio_page, PAGE_SIZE, 0) < PAGE_SIZE) {
		__submit_merged_bio(io);
		goto alloc_new;
	}

	if (fio->io_wbc)
		wbc_account_io(fio->io_wbc, bio_page, PAGE_SIZE);

	io->last_block_in_bio = fio->new_blkaddr;
	f2fs_trace_ios(fio, 0);

	trace_f2fs_submit_page_write(fio->page, fio);
skip:
	if (fio->in_list)
		goto next;
out:
	if (is_sbi_flag_set(sbi, SBI_IS_SHUTDOWN) ||
				!f2fs_is_checkpoint_ready(sbi))
		__submit_merged_bio(io);
	up_write(&io->io_rwsem);
}

static inline bool f2fs_need_verity(const struct inode *inode, pgoff_t idx)
{
	return fsverity_active(inode) &&
	       idx < DIV_ROUND_UP(inode->i_size, PAGE_SIZE);
}

static struct bio *f2fs_grab_read_bio(struct inode *inode, block_t blkaddr,
				      unsigned nr_pages, unsigned op_flag,
				      pgoff_t first_idx)
{
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
	struct bio *bio;
	struct bio_post_read_ctx *ctx;
	unsigned int post_read_steps = 0;

	bio = f2fs_bio_alloc(sbi, min_t(int, nr_pages, BIO_MAX_PAGES), false);
	if (!bio)
		return ERR_PTR(-ENOMEM);

	f2fs_set_bio_crypt_ctx(bio, inode, first_idx, NULL, GFP_NOFS);

	f2fs_target_device(sbi, blkaddr, bio);
	bio->bi_end_io = f2fs_read_end_io;
	bio_set_op_attrs(bio, REQ_OP_READ, op_flag);

	if (fscrypt_inode_uses_fs_layer_crypto(inode))
		post_read_steps |= 1 << STEP_DECRYPT;
	if (f2fs_compressed_file(inode))
		post_read_steps |= 1 << STEP_DECOMPRESS;
	if (f2fs_need_verity(inode, first_idx))
		post_read_steps |= 1 << STEP_VERITY;

	if (post_read_steps) {
		/* Due to the mempool, this never fails. */
		ctx = mempool_alloc(bio_post_read_ctx_pool, GFP_NOFS);
		ctx->bio = bio;
		ctx->sbi = sbi;
		ctx->enabled_steps = post_read_steps;
		bio->bi_private = ctx;
	}

	return bio;
}

static void f2fs_release_read_bio(struct bio *bio)
{
	if (bio->bi_private)
		mempool_free(bio->bi_private, bio_post_read_ctx_pool);
	bio_put(bio);
}

/* This can handle encryption stuffs */
static int f2fs_submit_page_read(struct inode *inode, struct page *page,
							block_t blkaddr)
{
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
	struct bio *bio;

	bio = f2fs_grab_read_bio(inode, blkaddr, 1, 0, page->index);
	if (IS_ERR(bio))
		return PTR_ERR(bio);

	/* wait for GCed page writeback via META_MAPPING */
	f2fs_wait_on_block_writeback(inode, blkaddr);

	if (bio_add_page(bio, page, PAGE_SIZE, 0) < PAGE_SIZE) {
		bio_put(bio);
		return -EFAULT;
	}
	ClearPageError(page);
	inc_page_count(sbi, F2FS_RD_DATA);
	__f2fs_submit_read_bio(sbi, bio, DATA);
	return 0;
}

static void __set_data_blkaddr(struct dnode_of_data *dn)
{
	struct f2fs_node *rn = F2FS_NODE(dn->node_page);
	__le32 *addr_array;
	int base = 0;
#ifdef F2FS_DELTA_COMPRESS
	int tmp_loc,last_iaddr=0;
	unsigned char ff1, ff2;
	char *dst_addr = NULL, *src_addr = NULL;
#endif

	if (IS_INODE(dn->node_page) && f2fs_has_extra_attr(dn->inode))
		base = get_extra_isize(dn->inode);

	/* Get physical address of data block */
	addr_array = blkaddr_in_node(rn);
	addr_array[base + dn->ofs_in_node] = cpu_to_le32(dn->data_blkaddr);
#ifdef F2FS_DELTA_COMPRESS
	if(is_inode_flag_set(dn->inode,FI_INLINE_DELTA)){
		dst_addr=kmalloc(PAGE_SIZE, GFP_NOFS);//cp inline to dst addr
		src_addr = inline_data_addr(dn->inode, dn->inode_page);
		memcpy(dst_addr, src_addr, MAX_INLINE_DATA(dn->inode));	
		tmp_loc=872*sizeof(__le32)-4;
		ff1=dst_addr[tmp_loc], ff2=dst_addr[tmp_loc-1];
		last_iaddr=ff2;
		last_iaddr = (last_iaddr << BITS_PER_BYTE) | ff1;
		last_iaddr=last_iaddr>dn->ofs_in_node?last_iaddr:dn->ofs_in_node;
		ff1=last_iaddr, ff2=last_iaddr>>BITS_PER_BYTE;
		dst_addr[tmp_loc]=ff1;
		dst_addr[tmp_loc-1]=ff2;
		memcpy(src_addr, dst_addr, MAX_INLINE_DATA(dn->inode));
	}	
#endif
}

/*
 * Lock ordering for the change of data block address:
 * ->data_page
 *  ->node_page
 *    update block addresses in the node page
 */
void f2fs_set_data_blkaddr(struct dnode_of_data *dn)
{
	f2fs_wait_on_page_writeback(dn->node_page, NODE, true, true);
	__set_data_blkaddr(dn);
	if (set_page_dirty(dn->node_page))
		dn->node_changed = true;
}

void f2fs_update_data_blkaddr(struct dnode_of_data *dn, block_t blkaddr)
{
	dn->data_blkaddr = blkaddr;
	f2fs_set_data_blkaddr(dn);
	f2fs_update_extent_cache(dn);
}

/* dn->ofs_in_node will be returned with up-to-date last block pointer */
int f2fs_reserve_new_blocks(struct dnode_of_data *dn, blkcnt_t count)
{
	struct f2fs_sb_info *sbi = F2FS_I_SB(dn->inode);
	int err;

	if (!count)
		return 0;

	if (unlikely(is_inode_flag_set(dn->inode, FI_NO_ALLOC)))
		return -EPERM;
	if (unlikely((err = inc_valid_block_count(sbi, dn->inode, &count))))
		return err;

	trace_f2fs_reserve_new_blocks(dn->inode, dn->nid,
						dn->ofs_in_node, count);

	f2fs_wait_on_page_writeback(dn->node_page, NODE, true, true);

	for (; count > 0; dn->ofs_in_node++) {
		block_t blkaddr = datablock_addr(dn->inode,
					dn->node_page, dn->ofs_in_node);
		if (blkaddr == NULL_ADDR) {
			dn->data_blkaddr = NEW_ADDR;
			__set_data_blkaddr(dn);
			count--;
		}
	}

	if (set_page_dirty(dn->node_page))
		dn->node_changed = true;
	return 0;
}

/* Should keep dn->ofs_in_node unchanged */
int f2fs_reserve_new_block(struct dnode_of_data *dn)
{
	unsigned int ofs_in_node = dn->ofs_in_node;
	int ret;

	ret = f2fs_reserve_new_blocks(dn, 1);
	dn->ofs_in_node = ofs_in_node;
	return ret;
}

int f2fs_reserve_block(struct dnode_of_data *dn, pgoff_t index)
{
	bool need_put = dn->inode_page ? false : true;
	int err;

	err = f2fs_get_dnode_of_data(dn, index, ALLOC_NODE);
	if (err)
		return err;

	if (dn->data_blkaddr == NULL_ADDR)
		err = f2fs_reserve_new_block(dn);
	if (err || need_put)
		f2fs_put_dnode(dn);
	return err;
}

int f2fs_get_block(struct dnode_of_data *dn, pgoff_t index)
{
	struct extent_info ei  = {0,0,0};
	struct inode *inode = dn->inode;

	if (f2fs_lookup_extent_cache(inode, index, &ei)) {
		dn->data_blkaddr = ei.blk + index - ei.fofs;
		return 0;
	}

	return f2fs_reserve_block(dn, index);
}

struct page *f2fs_get_read_data_page(struct inode *inode, pgoff_t index,
						int op_flags, bool for_write)
{
	struct address_space *mapping = inode->i_mapping;
	struct dnode_of_data dn;
	struct page *page;
	struct extent_info ei = {0,0,0};
	int err;

	page = f2fs_grab_cache_page(mapping, index, for_write);
	if (!page)
		return ERR_PTR(-ENOMEM);

	if (f2fs_lookup_extent_cache(inode, index, &ei)) {
		dn.data_blkaddr = ei.blk + index - ei.fofs;
		if (!f2fs_is_valid_blkaddr(F2FS_I_SB(inode), dn.data_blkaddr,
						DATA_GENERIC_ENHANCE_READ)) {
			err = -EFSCORRUPTED;
			goto put_err;
		}
		goto got_it;
	}

	set_new_dnode(&dn, inode, NULL, NULL, 0);
	err = f2fs_get_dnode_of_data(&dn, index, LOOKUP_NODE);
	if (err)
		goto put_err;
	f2fs_put_dnode(&dn);

	if (unlikely(dn.data_blkaddr == NULL_ADDR)) {
		err = -ENOENT;
		goto put_err;
	}
	if (dn.data_blkaddr != NEW_ADDR &&
			!f2fs_is_valid_blkaddr(F2FS_I_SB(inode),
						dn.data_blkaddr,
						DATA_GENERIC_ENHANCE)) {
		err = -EFSCORRUPTED;
		goto put_err;
	}
got_it:
	if (PageUptodate(page)) {
		unlock_page(page);
		return page;
	}

	/*
	 * A new dentry page is allocated but not able to be written, since its
	 * new inode page couldn't be allocated due to -ENOSPC.
	 * In such the case, its blkaddr can be remained as NEW_ADDR.
	 * see, f2fs_add_link -> f2fs_get_new_data_page ->
	 * f2fs_init_inode_metadata.
	 */
	if (dn.data_blkaddr == NEW_ADDR) {
		zero_user_segment(page, 0, PAGE_SIZE);
		if (!PageUptodate(page))
			SetPageUptodate(page);
		unlock_page(page);
		return page;
	}

	err = f2fs_submit_page_read(inode, page, dn.data_blkaddr);
	if (err)
		goto put_err;
	return page;

put_err:
	f2fs_put_page(page, 1);
	return ERR_PTR(err);
}

struct page *f2fs_find_data_page(struct inode *inode, pgoff_t index)
{
	struct address_space *mapping = inode->i_mapping;
	struct page *page;

	page = find_get_page(mapping, index);
	if (page && PageUptodate(page))
		return page;
	f2fs_put_page(page, 0);

	page = f2fs_get_read_data_page(inode, index, 0, false);
	if (IS_ERR(page))
		return page;

	if (PageUptodate(page))
		return page;

	wait_on_page_locked(page);
	if (unlikely(!PageUptodate(page))) {
		f2fs_put_page(page, 0);
		return ERR_PTR(-EIO);
	}
	return page;
}

/*
 * If it tries to access a hole, return an error.
 * Because, the callers, functions in dir.c and GC, should be able to know
 * whether this page exists or not.
 */
struct page *f2fs_get_lock_data_page(struct inode *inode, pgoff_t index,
							bool for_write)
{
	struct address_space *mapping = inode->i_mapping;
	struct page *page;
repeat:
	page = f2fs_get_read_data_page(inode, index, 0, for_write);
	if (IS_ERR(page))
		return page;

	/* wait for read completion */
	lock_page(page);
	if (unlikely(page->mapping != mapping)) {
		f2fs_put_page(page, 1);
		goto repeat;
	}
	if (unlikely(!PageUptodate(page))) {
		f2fs_put_page(page, 1);
		return ERR_PTR(-EIO);
	}
	return page;
}

/*
 * Caller ensures that this data page is never allocated.
 * A new zero-filled data page is allocated in the page cache.
 *
 * Also, caller should grab and release a rwsem by calling f2fs_lock_op() and
 * f2fs_unlock_op().
 * Note that, ipage is set only by make_empty_dir, and if any error occur,
 * ipage should be released by this function.
 */
struct page *f2fs_get_new_data_page(struct inode *inode,
		struct page *ipage, pgoff_t index, bool new_i_size)
{
	struct address_space *mapping = inode->i_mapping;
	struct page *page;
	struct dnode_of_data dn;
	int err;
#ifdef F2FS_DELTA_COMPRESS
	int offset[4];
	unsigned int noffset[4];
	int level;
	
	if(ipage==NULL) {
		level = f2fs_delta_get_node_path(inode, index, offset, noffset);
		if (level == 0 && offset[0]!=0)
		{			
			f2fs_retrieve_delta(inode, offset[0]);	
		}	
		else if(level>0)
		{
			f2fs_retrieve_inode_delta(inode);	
		}			
	}
#endif
	page = f2fs_grab_cache_page(mapping, index, true);
	if (!page) {
		/*
		 * before exiting, we should make sure ipage will be released
		 * if any error occur.
		 */
		f2fs_put_page(ipage, 1);
		return ERR_PTR(-ENOMEM);
	}

	set_new_dnode(&dn, inode, ipage, NULL, 0);
	err = f2fs_reserve_block(&dn, index);
	if (err) {
		f2fs_put_page(page, 1);
		return ERR_PTR(err);
	}
	if (!ipage)
		f2fs_put_dnode(&dn);

	if (PageUptodate(page))
		goto got_it;

	if (dn.data_blkaddr == NEW_ADDR) {
		zero_user_segment(page, 0, PAGE_SIZE);
		if (!PageUptodate(page))
			SetPageUptodate(page);
	} else {
		f2fs_put_page(page, 1);

		/* if ipage exists, blkaddr should be NEW_ADDR */
		f2fs_bug_on(F2FS_I_SB(inode), ipage);
		page = f2fs_get_lock_data_page(inode, index, true);
		if (IS_ERR(page))
			return page;
	}
got_it:
	if (new_i_size && i_size_read(inode) <
				((loff_t)(index + 1) << PAGE_SHIFT))
		f2fs_i_size_write(inode, ((loff_t)(index + 1) << PAGE_SHIFT));
	return page;
}

static int __allocate_data_block(struct dnode_of_data *dn, int seg_type)
{
	struct f2fs_sb_info *sbi = F2FS_I_SB(dn->inode);
	struct f2fs_summary sum;
	struct node_info ni;
	block_t old_blkaddr;
	blkcnt_t count = 1;
	int err;

	if (unlikely(is_inode_flag_set(dn->inode, FI_NO_ALLOC)))
		return -EPERM;

	err = f2fs_get_node_info(sbi, dn->nid, &ni);
	if (err)
		return err;

	dn->data_blkaddr = datablock_addr(dn->inode,
				dn->node_page, dn->ofs_in_node);
	if (dn->data_blkaddr != NULL_ADDR)
		goto alloc;

	if (unlikely((err = inc_valid_block_count(sbi, dn->inode, &count))))
		return err;

alloc:
	set_summary(&sum, dn->nid, dn->ofs_in_node, ni.version);
	old_blkaddr = dn->data_blkaddr;
#ifdef CONFIG_F2FS_BD_STAT
	bd_lock(sbi);
	bd_inc_array_val(sbi, hotcold_count, HC_DIRECT_IO, 1);
	bd_unlock(sbi);
#endif
	f2fs_allocate_data_block(sbi, NULL, old_blkaddr, &dn->data_blkaddr,
					&sum, seg_type, NULL, false);
	if (GET_SEGNO(sbi, old_blkaddr) != NULL_SEGNO)
		invalidate_mapping_pages(META_MAPPING(sbi),
					old_blkaddr, old_blkaddr);
	f2fs_update_data_blkaddr(dn, dn->data_blkaddr);

	/*
	 * i_size will be updated by direct_IO. Otherwise, we'll get stale
	 * data from unwritten block via dio_read.
	 */
	return 0;
}

int f2fs_preallocate_blocks(struct kiocb *iocb, struct iov_iter *from)
{
	struct inode *inode = file_inode(iocb->ki_filp);
	struct f2fs_map_blocks map;
	int flag;
	int err = 0;
	bool direct_io = iocb->ki_flags & IOCB_DIRECT;

	map.m_lblk = F2FS_BLK_ALIGN(iocb->ki_pos);
	map.m_len = F2FS_BYTES_TO_BLK(iocb->ki_pos + iov_iter_count(from));
	if (map.m_len > map.m_lblk)
		map.m_len -= map.m_lblk;
	else
		map.m_len = 0;

	map.m_next_pgofs = NULL;
	map.m_next_extent = NULL;
	map.m_seg_type = NO_CHECK_TYPE;
	map.m_may_create = true;

	if (direct_io) {
		map.m_seg_type = f2fs_rw_hint_to_seg_type(iocb->ki_hint);
		flag = f2fs_force_buffered_io(inode, iocb, from) ?
					F2FS_GET_BLOCK_PRE_AIO :
					F2FS_GET_BLOCK_PRE_DIO;
		goto map_blocks;
	}
	if (iocb->ki_pos + iov_iter_count(from) > MAX_INLINE_DATA(inode)) {
		err = f2fs_convert_inline_inode(inode);
		if (err)
			return err;
	}
	if (f2fs_has_inline_data(inode))
		return err;

	flag = F2FS_GET_BLOCK_PRE_AIO;

map_blocks:
	err = f2fs_map_blocks(inode, &map, 1, flag);
	if (map.m_len > 0 && err == -ENOSPC) {
		if (!direct_io)
			set_inode_flag(inode, FI_NO_PREALLOC);
		err = 0;
	}
	return err;
}

void __do_map_lock(struct f2fs_sb_info *sbi, int flag, bool lock)
{
	if (flag == F2FS_GET_BLOCK_PRE_AIO) {
		if (lock)
			down_read(&sbi->node_change);
		else
			up_read(&sbi->node_change);
	} else {
		if (lock)
			f2fs_lock_op(sbi);
		else
			f2fs_unlock_op(sbi);
	}
}

/*
 * f2fs_map_blocks() now supported readahead/bmap/rw direct_IO with
 * f2fs_map_blocks structure.
 * If original data blocks are allocated, then give them to blockdev.
 * Otherwise,
 *     a. preallocate requested block addresses
 *     b. do not use extent cache for better performance
 *     c. give the block addresses to blockdev
 */
int f2fs_map_blocks(struct inode *inode, struct f2fs_map_blocks *map,
						int create, int flag)
{
	unsigned int maxblocks = map->m_len;
	struct dnode_of_data dn;
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
	int mode = map->m_may_create ? ALLOC_NODE : LOOKUP_NODE;
	pgoff_t pgofs, end_offset, end;
	int err = 0, ofs = 1;
	unsigned int ofs_in_node, last_ofs_in_node;
	blkcnt_t prealloc;
	struct extent_info ei = {0,0,0};
	block_t blkaddr;
	unsigned int start_pgofs;
#ifdef F2FS_DELTA_COMPRESS
	int offset[4];
	unsigned int noffset[4];
	int level, last_iaddr, tmp_loc, size_thred=0;
	unsigned char ff1, ff2;
	char *dst_addr=NULL, *src_addr=NULL;
	struct page *ipage;
#endif
	if (!maxblocks)
		return 0;

	map->m_len = 0;
	map->m_flags = 0;

	/* it only supports block size == page size */
	pgofs =	(pgoff_t)map->m_lblk;
	end = pgofs + maxblocks;
#ifdef F2FS_DELTA_COMPRESS
	if(is_inode_flag_set(inode,FI_INLINE_DELTA)){
		level = f2fs_delta_get_node_path(inode, end, offset, noffset);
		ipage = f2fs_get_node_page(F2FS_I_SB(inode), inode->i_ino);
		if (IS_ERR(ipage)) {
			printk(KERN_ALERT"get ipage error in f2fs_map_blocks\n");
			if (level == 0 && offset[0]!=0)
			{			
				f2fs_retrieve_delta(inode, offset[0]);	
			}	
			else if(level>0)
			{
				f2fs_retrieve_inode_delta(inode);	
			}			
		}
		else
		{
			if (level == 0 && offset[0]!=0)
			{
				f2fs_wait_on_page_writeback(ipage, NODE, true, true);
				dst_addr=kmalloc(PAGE_SIZE, GFP_NOFS);//cp inline to dst addr
				src_addr = inline_data_addr(inode, ipage);
				memcpy(dst_addr, src_addr, MAX_INLINE_DATA(inode));	
				tmp_loc=872*sizeof(__le32)-4;
				ff1=dst_addr[tmp_loc], ff2=dst_addr[tmp_loc-1];
				last_iaddr=ff2;
				last_iaddr = (last_iaddr << BITS_PER_BYTE) | ff1;
				size_thred = 862*PAGE_SIZE;
				if(i_size_read(inode)<size_thred&&offset[0]<871&&(inode->i_blocks/4+1)<871){
					last_iaddr = last_iaddr < offset[0] ? offset[0] : last_iaddr;
					if(inode->i_blocks % 4 == 0) last_iaddr = last_iaddr < (inode->i_blocks/4) ? (inode->i_blocks/4) : last_iaddr;
					else last_iaddr = last_iaddr < (inode->i_blocks/4+1) ? (inode->i_blocks/4+1) : last_iaddr;
				}
				ff1=last_iaddr, ff2=last_iaddr>>BITS_PER_BYTE;
				dst_addr[tmp_loc]=ff1;
				dst_addr[tmp_loc-1]=ff2;
				memcpy(src_addr, dst_addr, MAX_INLINE_DATA(inode));	
				set_page_dirty(ipage);
				f2fs_put_page(ipage,1);
				f2fs_retrieve_delta(inode, last_iaddr);
			}	
			else if(level>0)
			{
				f2fs_retrieve_inode_delta(inode);	
			}
		}
	}
#endif
	if (!create && f2fs_lookup_extent_cache(inode, pgofs, &ei)) {
		if (test_opt(sbi, LFS) && flag == F2FS_GET_BLOCK_DIO &&
							map->m_may_create)
			goto next_dnode;

		map->m_pblk = ei.blk + pgofs - ei.fofs;
		map->m_len = min((pgoff_t)maxblocks, ei.fofs + ei.len - pgofs);
		map->m_flags = F2FS_MAP_MAPPED;
		if (map->m_next_extent)
			*map->m_next_extent = pgofs + map->m_len;

		if (flag == F2FS_GET_BLOCK_DIO)
			f2fs_wait_on_block_writeback_range(inode,
						map->m_pblk, map->m_len);
		goto out;
	}

next_dnode:
	if (map->m_may_create)
		__do_map_lock(sbi, flag, true);

	/* When reading holes, we need its node page */
	set_new_dnode(&dn, inode, NULL, NULL, 0);
	err = f2fs_get_dnode_of_data(&dn, pgofs, mode);
	if (err) {
		if (flag == F2FS_GET_BLOCK_BMAP)
			map->m_pblk = 0;
		if (err == -ENOENT) {
			err = 0;
			if (map->m_next_pgofs)
				*map->m_next_pgofs =
					f2fs_get_next_page_offset(&dn, pgofs);
			if (map->m_next_extent)
				*map->m_next_extent =
					f2fs_get_next_page_offset(&dn, pgofs);
		}
		goto unlock_out;
	}

	start_pgofs = pgofs;
	prealloc = 0;
	last_ofs_in_node = ofs_in_node = dn.ofs_in_node;
	end_offset = ADDRS_PER_PAGE(dn.node_page, inode);

next_block:
	blkaddr = datablock_addr(dn.inode, dn.node_page, dn.ofs_in_node);

	if (__is_valid_data_blkaddr(blkaddr) &&
		!f2fs_is_valid_blkaddr(sbi, blkaddr, DATA_GENERIC_ENHANCE)) {
		printk(KERN_ALERT"invalid blkaddr in map blocks:%d %d %d\n",blkaddr, inode->i_ino, dn.ofs_in_node);
		err = -EFSCORRUPTED;
		goto sync_out;
	}

	if (__is_valid_data_blkaddr(blkaddr)) {
		/* use out-place-update for driect IO under LFS mode */
		if (test_opt(sbi, LFS) && flag == F2FS_GET_BLOCK_DIO &&
							map->m_may_create) {
			err = __allocate_data_block(&dn, map->m_seg_type);
			if (err)
				goto sync_out;
			blkaddr = dn.data_blkaddr;
			set_inode_flag(inode, FI_APPEND_WRITE);
		}
	} else {
		if (create) {
			if (unlikely(f2fs_cp_error(sbi))) {
				err = -EIO;
				goto sync_out;
			}
			if (flag == F2FS_GET_BLOCK_PRE_AIO) {
				if (blkaddr == NULL_ADDR) {
					prealloc++;
					last_ofs_in_node = dn.ofs_in_node;
				}
			} else {
				WARN_ON(flag != F2FS_GET_BLOCK_PRE_DIO &&
					flag != F2FS_GET_BLOCK_DIO);
				err = __allocate_data_block(&dn,
							map->m_seg_type);
				if (!err)
					set_inode_flag(inode, FI_APPEND_WRITE);
			}
			if (err)
				goto sync_out;
			map->m_flags |= F2FS_MAP_NEW;
			blkaddr = dn.data_blkaddr;
		} else {
			if (flag == F2FS_GET_BLOCK_BMAP) {
				map->m_pblk = 0;
				goto sync_out;
			}
			if (flag == F2FS_GET_BLOCK_PRECACHE)
				goto sync_out;
			if (flag == F2FS_GET_BLOCK_FIEMAP &&
						blkaddr == NULL_ADDR) {
				if (map->m_next_pgofs)
					*map->m_next_pgofs = pgofs + 1;
				goto sync_out;
			}
			if (flag != F2FS_GET_BLOCK_FIEMAP) {
				/* for defragment case */
				if (map->m_next_pgofs)
					*map->m_next_pgofs = pgofs + 1;
				goto sync_out;
			}
		}
	}

	if (flag == F2FS_GET_BLOCK_PRE_AIO)
		goto skip;

	if (map->m_len == 0) {
		/* preallocated unwritten block should be mapped for fiemap. */
		if (blkaddr == NEW_ADDR)
			map->m_flags |= F2FS_MAP_UNWRITTEN;
		map->m_flags |= F2FS_MAP_MAPPED;

		map->m_pblk = blkaddr;
		map->m_len = 1;
	} else if ((map->m_pblk != NEW_ADDR &&
			blkaddr == (map->m_pblk + ofs)) ||
			(map->m_pblk == NEW_ADDR && blkaddr == NEW_ADDR) ||
			flag == F2FS_GET_BLOCK_PRE_DIO) {
		ofs++;
		map->m_len++;
	} else {
		goto sync_out;
	}

skip:
	dn.ofs_in_node++;
	pgofs++;

	/* preallocate blocks in batch for one dnode page */
	if (flag == F2FS_GET_BLOCK_PRE_AIO &&
			(pgofs == end || dn.ofs_in_node == end_offset)) {

		dn.ofs_in_node = ofs_in_node;
		err = f2fs_reserve_new_blocks(&dn, prealloc);
		if (err)
			goto sync_out;

		map->m_len += dn.ofs_in_node - ofs_in_node;
		if (prealloc && dn.ofs_in_node != last_ofs_in_node + 1) {
			err = -ENOSPC;
			goto sync_out;
		}
		dn.ofs_in_node = end_offset;
	}

	if (pgofs >= end)
		goto sync_out;
	else if (dn.ofs_in_node < end_offset)
		goto next_block;

	if (flag == F2FS_GET_BLOCK_PRECACHE) {
		if (map->m_flags & F2FS_MAP_MAPPED) {
			unsigned int ofs = start_pgofs - map->m_lblk;

			f2fs_update_extent_cache_range(&dn,
				start_pgofs, map->m_pblk + ofs,
				map->m_len - ofs);
		}
	}

	f2fs_put_dnode(&dn);

	if (map->m_may_create) {
		__do_map_lock(sbi, flag, false);
		f2fs_balance_fs(sbi, dn.node_changed);
	}
	goto next_dnode;

sync_out:

	if (flag == F2FS_GET_BLOCK_DIO && map->m_flags & F2FS_MAP_MAPPED)
		f2fs_wait_on_block_writeback_range(inode,
						map->m_pblk, map->m_len);

	if (flag == F2FS_GET_BLOCK_PRECACHE) {
		if (map->m_flags & F2FS_MAP_MAPPED) {
			unsigned int ofs = start_pgofs - map->m_lblk;

			f2fs_update_extent_cache_range(&dn,
				start_pgofs, map->m_pblk + ofs,
				map->m_len - ofs);
		}
		if (map->m_next_extent)
			*map->m_next_extent = pgofs + 1;
	}
	f2fs_put_dnode(&dn);
unlock_out:
	if (map->m_may_create) {
		__do_map_lock(sbi, flag, false);
		f2fs_balance_fs(sbi, dn.node_changed);
	}
out:
	trace_f2fs_map_blocks(inode, map, err);
	return err;
}

bool f2fs_overwrite_io(struct inode *inode, loff_t pos, size_t len)
{
	struct f2fs_map_blocks map;
	block_t last_lblk;
	int err;

	if (pos + len > i_size_read(inode))
		return false;

	map.m_lblk = F2FS_BYTES_TO_BLK(pos);
	map.m_next_pgofs = NULL;
	map.m_next_extent = NULL;
	map.m_seg_type = NO_CHECK_TYPE;
	map.m_may_create = false;
	last_lblk = F2FS_BLK_ALIGN(pos + len);

	while (map.m_lblk < last_lblk) {
		map.m_len = last_lblk - map.m_lblk;
		err = f2fs_map_blocks(inode, &map, 0, F2FS_GET_BLOCK_DEFAULT);
		if (err || map.m_len == 0)
			return false;
		map.m_lblk += map.m_len;
	}
	return true;
}

static int __get_data_block(struct inode *inode, sector_t iblock,
			struct buffer_head *bh, int create, int flag,
			pgoff_t *next_pgofs, int seg_type, bool may_write)
{
	struct f2fs_map_blocks map;
	int err;

	map.m_lblk = iblock;
	map.m_len = bh->b_size >> inode->i_blkbits;
	map.m_next_pgofs = next_pgofs;
	map.m_next_extent = NULL;
	map.m_seg_type = seg_type;
	map.m_may_create = may_write;

	err = f2fs_map_blocks(inode, &map, create, flag);
	if (!err) {
		map_bh(bh, inode->i_sb, map.m_pblk);
		bh->b_state = (bh->b_state & ~F2FS_MAP_FLAGS) | map.m_flags;
		bh->b_size = (u64)map.m_len << inode->i_blkbits;
	}
	return err;
}

static int get_data_block(struct inode *inode, sector_t iblock,
			struct buffer_head *bh_result, int create, int flag,
			pgoff_t *next_pgofs)
{
	return __get_data_block(inode, iblock, bh_result, create,
							flag, next_pgofs,
							NO_CHECK_TYPE, create);
}

static int get_data_block_dio_write(struct inode *inode, sector_t iblock,
			struct buffer_head *bh_result, int create)
{
	return __get_data_block(inode, iblock, bh_result, create,
				F2FS_GET_BLOCK_DIO, NULL,
				f2fs_rw_hint_to_seg_type(inode->i_write_hint),
				IS_SWAPFILE(inode) ? false : true);
}

static int get_data_block_dio(struct inode *inode, sector_t iblock,
			struct buffer_head *bh_result, int create)
{
	return __get_data_block(inode, iblock, bh_result, create,
				F2FS_GET_BLOCK_DIO, NULL,
				f2fs_rw_hint_to_seg_type(inode->i_write_hint),
				false);
}

static int get_data_block_bmap(struct inode *inode, sector_t iblock,
			struct buffer_head *bh_result, int create)
{
	/* Block number less than F2FS MAX BLOCKS */
	if (unlikely(iblock >= F2FS_I_SB(inode)->max_file_blocks))
		return -EFBIG;

	return __get_data_block(inode, iblock, bh_result, create,
						F2FS_GET_BLOCK_BMAP, NULL,
						NO_CHECK_TYPE, create);
}

static inline sector_t logical_to_blk(struct inode *inode, loff_t offset)
{
	return (offset >> inode->i_blkbits);
}

static inline loff_t blk_to_logical(struct inode *inode, sector_t blk)
{
	return (blk << inode->i_blkbits);
}

static int f2fs_xattr_fiemap(struct inode *inode,
				struct fiemap_extent_info *fieinfo)
{
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
	struct page *page;
	struct node_info ni;
	__u64 phys = 0, len;
	__u32 flags;
	nid_t xnid = F2FS_I(inode)->i_xattr_nid;
	int err = 0;

	if (f2fs_has_inline_xattr(inode)) {
		int offset;

		page = f2fs_grab_cache_page(NODE_MAPPING(sbi),
						inode->i_ino, false);
		if (!page)
			return -ENOMEM;

		err = f2fs_get_node_info(sbi, inode->i_ino, &ni);
		if (err) {
			f2fs_put_page(page, 1);
			return err;
		}

		phys = (__u64)blk_to_logical(inode, ni.blk_addr);
		offset = offsetof(struct f2fs_inode, i_addr) +
					sizeof(__le32) * (DEF_ADDRS_PER_INODE -
					get_inline_xattr_addrs(inode));

		phys += offset;
		len = inline_xattr_size(inode);

		f2fs_put_page(page, 1);

		flags = FIEMAP_EXTENT_DATA_INLINE | FIEMAP_EXTENT_NOT_ALIGNED;

		if (!xnid)
			flags |= FIEMAP_EXTENT_LAST;

		err = fiemap_fill_next_extent(fieinfo, 0, phys, len, flags);
		if (err || err == 1)
			return err;
	}

	if (xnid) {
		page = f2fs_grab_cache_page(NODE_MAPPING(sbi), xnid, false);
		if (!page)
			return -ENOMEM;

		err = f2fs_get_node_info(sbi, xnid, &ni);
		if (err) {
			f2fs_put_page(page, 1);
			return err;
		}

		phys = (__u64)blk_to_logical(inode, ni.blk_addr);
		len = inode->i_sb->s_blocksize;

		f2fs_put_page(page, 1);

		flags = FIEMAP_EXTENT_LAST;
	}

	if (phys)
		err = fiemap_fill_next_extent(fieinfo, 0, phys, len, flags);

	return (err < 0 ? err : 0);
}

int f2fs_fiemap(struct inode *inode, struct fiemap_extent_info *fieinfo,
		u64 start, u64 len)
{
	struct buffer_head map_bh;
	sector_t start_blk, last_blk;
	pgoff_t next_pgofs;
	u64 logical = 0, phys = 0, size = 0;
	u32 flags = 0;
	int ret = 0;

	if (fieinfo->fi_flags & FIEMAP_FLAG_CACHE) {
		ret = f2fs_precache_extents(inode);
		if (ret)
			return ret;
	}

	ret = fiemap_check_flags(fieinfo, FIEMAP_FLAG_SYNC | FIEMAP_FLAG_XATTR);
	if (ret)
		return ret;

	inode_lock(inode);

	if (fieinfo->fi_flags & FIEMAP_FLAG_XATTR) {
		ret = f2fs_xattr_fiemap(inode, fieinfo);
		goto out;
	}

	if (f2fs_has_inline_data(inode) || f2fs_has_inline_dentry(inode)) {
		ret = f2fs_inline_data_fiemap(inode, fieinfo, start, len);
		if (ret != -EAGAIN)
			goto out;
	}

	if (logical_to_blk(inode, len) == 0)
		len = blk_to_logical(inode, 1);

	start_blk = logical_to_blk(inode, start);
	last_blk = logical_to_blk(inode, start + len - 1);

next:
	memset(&map_bh, 0, sizeof(struct buffer_head));
	map_bh.b_size = len;

	ret = get_data_block(inode, start_blk, &map_bh, 0,
					F2FS_GET_BLOCK_FIEMAP, &next_pgofs);
	if (ret)
		goto out;

	/* HOLE */
	if (!buffer_mapped(&map_bh)) {
		start_blk = next_pgofs;

		if (blk_to_logical(inode, start_blk) < blk_to_logical(inode,
					F2FS_I_SB(inode)->max_file_blocks))
			goto prep_next;

		flags |= FIEMAP_EXTENT_LAST;
	}

	if (size) {
		if (IS_ENCRYPTED(inode))
			flags |= FIEMAP_EXTENT_DATA_ENCRYPTED;

		ret = fiemap_fill_next_extent(fieinfo, logical,
				phys, size, flags);
	}

	if (start_blk > last_blk || ret)
		goto out;

	logical = blk_to_logical(inode, start_blk);
	phys = blk_to_logical(inode, map_bh.b_blocknr);
	size = map_bh.b_size;
	flags = 0;
	if (buffer_unwritten(&map_bh))
		flags = FIEMAP_EXTENT_UNWRITTEN;

	start_blk += logical_to_blk(inode, size);

prep_next:
	cond_resched();
	if (fatal_signal_pending(current))
		ret = -EINTR;
	else
		goto next;
out:
	if (ret == 1)
		ret = 0;

	inode_unlock(inode);
	return ret;
}

static inline loff_t f2fs_readpage_limit(struct inode *inode)
{
	if (IS_ENABLED(CONFIG_FS_VERITY) &&
	    (IS_VERITY(inode) || f2fs_verity_in_progress(inode)))
		return inode->i_sb->s_maxbytes;

	return i_size_read(inode);
}

static int f2fs_read_single_page(struct inode *inode, struct page *page,
					unsigned nr_pages,
					struct f2fs_map_blocks *map,
					struct bio **bio_ret,
					sector_t *last_block_in_bio,
					bool is_readahead)
{
	struct bio *bio = *bio_ret;
	const unsigned blkbits = inode->i_blkbits;
	const unsigned blocksize = 1 << blkbits;
	sector_t block_in_file;
	sector_t last_block;
	sector_t last_block_in_file;
	sector_t block_nr;
	int ret = 0;

	block_in_file = (sector_t)page_index(page);
	last_block = block_in_file + nr_pages;
	last_block_in_file = (f2fs_readpage_limit(inode) + blocksize - 1) >>
							blkbits;
	if (last_block > last_block_in_file)
		last_block = last_block_in_file;

	/* just zeroing out page which is beyond EOF */
	if (block_in_file >= last_block)
		goto zero_out;
	/*
	 * Map blocks using the previous result first.
	 */
	if ((map->m_flags & F2FS_MAP_MAPPED) &&
			block_in_file > map->m_lblk &&
			block_in_file < (map->m_lblk + map->m_len))
		goto got_it;

	/*
	 * Then do more f2fs_map_blocks() calls until we are
	 * done with this page.
	 */
	map->m_lblk = block_in_file;
	map->m_len = last_block - block_in_file;

	ret = f2fs_map_blocks(inode, map, 0, F2FS_GET_BLOCK_DEFAULT);
	if (ret)
		goto out;
got_it:
	if ((map->m_flags & F2FS_MAP_MAPPED)) {
		block_nr = map->m_pblk + block_in_file - map->m_lblk;
		SetPageMappedToDisk(page);

		if (!PageUptodate(page) && (!PageSwapCache(page) &&
					!cleancache_get_page(page))) {
			SetPageUptodate(page);
			goto confused;
		}

		if (!f2fs_is_valid_blkaddr(F2FS_I_SB(inode), block_nr,
						DATA_GENERIC_ENHANCE_READ)) {
			ret = -EFSCORRUPTED;
			goto out;
		}
	} else {
zero_out:
		zero_user_segment(page, 0, PAGE_SIZE);
		if (f2fs_need_verity(inode, page->index) &&
		    !fsverity_verify_page(page)) {
			ret = -EIO;
			goto out;
		}
		if (!PageUptodate(page))
			SetPageUptodate(page);
		unlock_page(page);
		goto out;
	}

	/*
	 * This page will go to BIO.  Do we need to send this
	 * BIO off first?
	 */
	if (bio && (!page_is_mergeable(F2FS_I_SB(inode), bio,
				       *last_block_in_bio, block_nr) ||
		    !f2fs_crypt_mergeable_bio(bio, inode, page->index, NULL))) {
submit_and_realloc:
		__f2fs_submit_read_bio(F2FS_I_SB(inode), bio, DATA);
		bio = NULL;
	}

	if (bio == NULL) {
		bio = f2fs_grab_read_bio(inode, block_nr, nr_pages,
				is_readahead ? REQ_RAHEAD : 0, page->index);
		if (IS_ERR(bio)) {
			ret = PTR_ERR(bio);
			bio = NULL;
			goto out;
		}
	}

	/*
	 * If the page is under writeback, we need to wait for
	 * its completion to see the correct decrypted data.
	 */
	f2fs_wait_on_block_writeback(inode, block_nr);

	if (bio_add_page(bio, page, blocksize, 0) < blocksize)
		goto submit_and_realloc;

	inc_page_count(F2FS_I_SB(inode), F2FS_RD_DATA);
	ClearPageError(page);
	*last_block_in_bio = block_nr;
	goto out;
confused:
	if (bio) {
		__f2fs_submit_read_bio(F2FS_I_SB(inode), bio, DATA);
		bio = NULL;
	}
	unlock_page(page);
out:
	*bio_ret = bio;
	return ret;
}

#ifdef CONFIG_F2FS_FS_COMPRESSION
int f2fs_read_multi_pages(struct compress_ctx *cc, struct bio **bio_ret,
				unsigned nr_pages, sector_t *last_block_in_bio,
				bool is_readahead)
{
	struct dnode_of_data dn;
	struct inode *inode = cc->inode;
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
	struct bio *bio = *bio_ret;
	unsigned int start_idx = cc->cluster_idx << cc->log_cluster_size;
	sector_t last_block_in_file;
	const unsigned blkbits = inode->i_blkbits;
	const unsigned blocksize = 1 << blkbits;
	struct decompress_io_ctx *dic = NULL;
	int i;
	int ret = 0;

	f2fs_bug_on(sbi, f2fs_cluster_is_empty(cc));

	last_block_in_file = (i_size_read(inode) + blocksize - 1) >> blkbits;

	/* get rid of pages beyond EOF */
	for (i = 0; i < cc->cluster_size; i++) {
		struct page *page = cc->rpages[i];

		if (!page)
			continue;
		if ((sector_t)page->index >= last_block_in_file) {
			zero_user_segment(page, 0, PAGE_SIZE);
			if (!PageUptodate(page))
				SetPageUptodate(page);
		} else if (!PageUptodate(page)) {
			continue;
		}
		unlock_page(page);
		cc->rpages[i] = NULL;
		cc->nr_rpages--;
	}

	/* we are done since all pages are beyond EOF */
	if (f2fs_cluster_is_empty(cc))
		goto out;

	set_new_dnode(&dn, inode, NULL, NULL, 0);
	ret = f2fs_get_dnode_of_data(&dn, start_idx, LOOKUP_NODE);
	if (ret)
		goto out;

	/* cluster was overwritten as normal cluster */
	if (dn.data_blkaddr != COMPRESS_ADDR)
		goto out;

	for (i = 1; i < cc->cluster_size; i++) {
		block_t blkaddr;

		blkaddr = datablock_addr(dn.inode, dn.node_page,
						dn.ofs_in_node + i);

		if (!__is_valid_data_blkaddr(blkaddr))
			break;

		if (!f2fs_is_valid_blkaddr(sbi, blkaddr, DATA_GENERIC)) {
			ret = -EFAULT;
			goto out_put_dnode;
		}
		cc->nr_cpages++;
	}

	/* nothing to decompress */
	if (cc->nr_cpages == 0) {
		ret = 0;
		goto out_put_dnode;
	}

	dic = f2fs_alloc_dic(cc);
	if (IS_ERR(dic)) {
		ret = PTR_ERR(dic);
		goto out_put_dnode;
	}

	for (i = 0; i < dic->nr_cpages; i++) {
		struct page *page = dic->cpages[i];
		block_t blkaddr;

		blkaddr = datablock_addr(dn.inode, dn.node_page,
						dn.ofs_in_node + i + 1);

		if (bio && (!page_is_mergeable(sbi, bio,
					*last_block_in_bio, blkaddr) ||
		    !f2fs_crypt_mergeable_bio(bio, inode, page->index, NULL))) {
submit_and_realloc:
			__submit_bio(sbi, bio, DATA);
			bio = NULL;
		}

		if (!bio) {
			bio = f2fs_grab_read_bio(inode, blkaddr, nr_pages,
					is_readahead ? REQ_RAHEAD : 0,
					page->index);
			if (IS_ERR(bio)) {
				ret = PTR_ERR(bio);
				bio = NULL;
				dic->failed = true;
				if (refcount_sub_and_test(dic->nr_cpages - i,
							&dic->ref))
					f2fs_decompress_end_io(dic->rpages,
							cc->cluster_size, true,
							false);
				f2fs_free_dic(dic);
				f2fs_put_dnode(&dn);
				*bio_ret = bio;
				return ret;
			}
		}

		f2fs_wait_on_block_writeback(inode, blkaddr);

		if (bio_add_page(bio, page, blocksize, 0) < blocksize)
			goto submit_and_realloc;

		inc_page_count(sbi, F2FS_RD_DATA);
		ClearPageError(page);
		*last_block_in_bio = blkaddr;
	}

	f2fs_put_dnode(&dn);

	*bio_ret = bio;
	return 0;

out_put_dnode:
	f2fs_put_dnode(&dn);
out:
	f2fs_decompress_end_io(cc->rpages, cc->cluster_size, true, false);
	*bio_ret = bio;
	return ret;
}
#endif

/*
 * This function was originally taken from fs/mpage.c, and customized for f2fs.
 * Major change was from block_size == page_size in f2fs by default.
 *
 * Note that the aops->readpages() function is ONLY used for read-ahead. If
 * this function ever deviates from doing just read-ahead, it should either
 * use ->readpage() or do the necessary surgery to decouple ->readpages()
 * from read-ahead.
 */
int f2fs_mpage_readpages(struct address_space *mapping,
			struct list_head *pages, struct page *page,
			unsigned nr_pages, bool is_readahead)
{
	struct bio *bio = NULL;
	sector_t last_block_in_bio = 0;
	struct inode *inode = mapping->host;
	struct f2fs_map_blocks map;
#ifdef CONFIG_F2FS_FS_COMPRESSION
	struct compress_ctx cc = {
		.inode = inode,
		.log_cluster_size = F2FS_I(inode)->i_log_cluster_size,
		.cluster_size = F2FS_I(inode)->i_cluster_size,
		.cluster_idx = NULL_CLUSTER,
		.rpages = NULL,
		.cpages = NULL,
		.nr_rpages = 0,
		.nr_cpages = 0,
	};
#endif
	unsigned max_nr_pages = nr_pages;
	int ret = 0;

	map.m_pblk = 0;
	map.m_lblk = 0;
	map.m_len = 0;
	map.m_flags = 0;
	map.m_next_pgofs = NULL;
	map.m_next_extent = NULL;
	map.m_seg_type = NO_CHECK_TYPE;
	map.m_may_create = false;

	for (; nr_pages; nr_pages--) {
		if (pages) {
			page = list_last_entry(pages, struct page, lru);

			prefetchw(&page->flags);
			list_del(&page->lru);
			if (add_to_page_cache_lru(page, mapping,
						  page_index(page),
						  readahead_gfp_mask(mapping)))
				goto next_page;
		}

#ifdef CONFIG_F2FS_FS_COMPRESSION
		if (f2fs_compressed_file(inode)) {
			/* there are remained comressed pages, submit them */
			if (!f2fs_cluster_can_merge_page(&cc, page->index)) {
				ret = f2fs_read_multi_pages(&cc, &bio,
							max_nr_pages,
							&last_block_in_bio,
							is_readahead);
				f2fs_destroy_compress_ctx(&cc);
				if (ret)
					goto set_error_page;
			}
			ret = f2fs_is_compressed_cluster(inode, page->index);
			if (ret < 0)
				goto set_error_page;
			else if (!ret)
				goto read_single_page;

			ret = f2fs_init_compress_ctx(&cc);
			if (ret)
				goto set_error_page;

			f2fs_compress_ctx_add_page(&cc, page);

			goto next_page;
		}
read_single_page:
#endif

		ret = f2fs_read_single_page(inode, page, max_nr_pages, &map,
					&bio, &last_block_in_bio, is_readahead);
		if (ret) {
#ifdef CONFIG_F2FS_FS_COMPRESSION
set_error_page:
#endif
			SetPageError(page);
			zero_user_segment(page, 0, PAGE_SIZE);
			unlock_page(page);
		}

next_page:
		if (pages)
			put_page(page);

#ifdef CONFIG_F2FS_FS_COMPRESSION
		if (f2fs_compressed_file(inode)) {
			/* last page */
			if (nr_pages == 1 && !f2fs_cluster_is_empty(&cc)) {
				ret = f2fs_read_multi_pages(&cc, &bio,
							max_nr_pages,
							&last_block_in_bio,
							is_readahead);
				f2fs_destroy_compress_ctx(&cc);
			}
		}
#endif
	}
	BUG_ON(pages && !list_empty(pages));
	
	if (bio){
		__f2fs_submit_read_bio(F2FS_I_SB(inode), bio, DATA);
	}
	return pages ? 0 : ret;
}

static int f2fs_read_data_page(struct file *file, struct page *page)
{
	struct inode *inode = page_file_mapping(page)->host;
	int ret = -EAGAIN;
#ifdef F2FS_DELTA_COMPRESS
	int flag=0;
#endif
	trace_f2fs_readpage(page, DATA);

	if (!f2fs_is_compress_backend_ready(inode)) {
		unlock_page(page);
		return -EOPNOTSUPP;
	}
#ifdef F2FS_DELTA_COMPRESS
wait_truncate:
	if(is_inode_flag_set(inode, FI_DELTA_TRUNCATING)) {
		congestion_wait(BLK_RW_ASYNC, HZ/50);
		if(PageLocked(page)) {
			printk(KERN_ALERT"locked page in read data page\n");
			f2fs_put_page(page,1);
			flag=1;
		}
		goto wait_truncate;
	}
	if(flag) {
		if(!trylock_page(page)) {
			printk(KERN_ALERT"lock page failed in read data page\n");
			congestion_wait(BLK_RW_ASYNC, HZ/50);
			goto wait_truncate;
		}
	}
#endif
	/* If the file has inline data, try to read it directly */
	if (f2fs_has_inline_data(inode))
		ret = f2fs_read_inline_data(inode, page);
	if (ret == -EAGAIN){
		ret = f2fs_mpage_readpages(page_file_mapping(page),
						NULL, page, 1, false);
#ifdef F2FS_DELTA_COMPRESS
		f2fs_decompress_delta(page);
#ifdef F2FS_MAIN_COMPRESS
		if(is_inode_flag_set(inode, FI_MAIN_DELTA)){
			f2fs_decompress_main(page);
		}
#endif
#endif
	}
	return ret;
}

static int f2fs_read_data_pages(struct file *file,
			struct address_space *mapping,
			struct list_head *pages, unsigned nr_pages)
{
	struct inode *inode = mapping->host;
	struct page *page = list_last_entry(pages, struct page, lru);
#ifdef F2FS_DELTA_COMPRESS
	int base_index[nr_pages];
	int i=0,ret=0,flag=0;
	struct page *base_page;
	memset(base_index, 0, sizeof(int)*nr_pages);
#endif
	trace_f2fs_readpages(inode, page, nr_pages);

	if (!f2fs_is_compress_backend_ready(inode))
		return 0;

	/* If the file has inline data, skip readpages */
	if (f2fs_has_inline_data(inode))
		return 0;
#ifdef F2FS_DELTA_COMPRESS
wait_truncate:
	list_for_each_entry_reverse(base_page, pages, lru){
		if(is_inode_flag_set(inode, FI_DELTA_TRUNCATING)) {
			congestion_wait(BLK_RW_ASYNC, HZ/50);
			if(PageLocked(base_page)) {
				printk(KERN_ALERT"locked page in read data pages\n");
				f2fs_put_page(base_page,1);
				flag=1;
			}
			goto wait_truncate;
		}
		if(flag) {
			if(!trylock_page(base_page)) {
				printk(KERN_ALERT"lock page failed in read data pages\n");
				congestion_wait(BLK_RW_ASYNC, HZ/50);
				goto wait_truncate;
			}
		}
		base_index[i]=base_page->index;
		i++;
	}
	ret=f2fs_mpage_readpages(mapping, pages, NULL, nr_pages, true);
	for(i=0;i<nr_pages;i++){
		base_page=find_get_entry(mapping, base_index[i]);
		if (!base_page) 
		{
			printk(KERN_ALERT"null page in read data pages:%d %d\n",base_index[i],inode->i_ino);
			continue;
		}
		f2fs_decompress_delta(base_page);
#ifdef F2FS_MAIN_COMPRESS
		if(is_inode_flag_set(inode, FI_MAIN_DELTA)){
			f2fs_decompress_main(page);
		}
#endif
	}
	return ret;
#else
	return f2fs_mpage_readpages(mapping, pages, NULL, nr_pages, true);
#endif
}

int f2fs_encrypt_one_page(struct f2fs_io_info *fio)
{
	struct inode *inode = fio->page->mapping->host;
	struct page *mpage, *page;
	gfp_t gfp_flags = GFP_NOFS;

	if (!f2fs_encrypted_file(inode))
		return 0;

	page = fio->compressed_page ? fio->compressed_page : fio->page;

	/* wait for GCed page writeback via META_MAPPING */
	f2fs_wait_on_block_writeback(inode, fio->old_blkaddr);

	if (fscrypt_inode_uses_inline_crypto(inode))
		return 0;

retry_encrypt:
	fio->encrypted_page = fscrypt_encrypt_pagecache_blocks(page,
					PAGE_SIZE, 0, gfp_flags);
	if (IS_ERR(fio->encrypted_page)) {
		/* flush pending IOs and wait for a while in the ENOMEM case */
		if (PTR_ERR(fio->encrypted_page) == -ENOMEM) {
			f2fs_flush_merged_writes(fio->sbi);
			congestion_wait(BLK_RW_ASYNC, HZ/50);
			gfp_flags |= __GFP_NOFAIL;
			goto retry_encrypt;
		}
		return PTR_ERR(fio->encrypted_page);
	}

	mpage = find_lock_page(META_MAPPING(fio->sbi), fio->old_blkaddr);
	if (mpage) {
		if (PageUptodate(mpage))
			memcpy(page_address(mpage),
				page_address(fio->encrypted_page), PAGE_SIZE);
		f2fs_put_page(mpage, 1);
	}
	return 0;
}

static inline bool check_inplace_update_policy(struct inode *inode,
				struct f2fs_io_info *fio)
{
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
	unsigned int policy = SM_I(sbi)->ipu_policy;

	if (policy & (0x1 << F2FS_IPU_FORCE))
		return true;
	if (policy & (0x1 << F2FS_IPU_SSR) && f2fs_need_SSR(sbi))
		return true;
	if (policy & (0x1 << F2FS_IPU_UTIL) &&
			utilization(sbi) > SM_I(sbi)->min_ipu_util)
		return true;
	if (policy & (0x1 << F2FS_IPU_SSR_UTIL) && f2fs_need_SSR(sbi) &&
			utilization(sbi) > SM_I(sbi)->min_ipu_util)
		return true;

	/*
	 * IPU for rewrite async pages
	 */
	if (policy & (0x1 << F2FS_IPU_ASYNC) &&
			fio && fio->op == REQ_OP_WRITE &&
			!(fio->op_flags & REQ_SYNC) &&
			!IS_ENCRYPTED(inode))
		return true;

	/* this is only set during fdatasync */
	if (policy & (0x1 << F2FS_IPU_FSYNC) &&
			is_inode_flag_set(inode, FI_NEED_IPU))
		return true;

	if (unlikely(fio && is_sbi_flag_set(sbi, SBI_CP_DISABLED) &&
			!f2fs_is_checkpointed_data(sbi, fio->old_blkaddr)))
		return true;

	return false;
}

bool f2fs_should_update_inplace(struct inode *inode, struct f2fs_io_info *fio)
{
	if (f2fs_is_pinned_file(inode))
		return true;

	/* if this is cold file, we should overwrite to avoid fragmentation */
	if (file_is_cold(inode))
		return true;

	return check_inplace_update_policy(inode, fio);
}

bool f2fs_should_update_outplace(struct inode *inode, struct f2fs_io_info *fio)
{
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);

	if (test_opt(sbi, LFS))
		return true;
	if (S_ISDIR(inode->i_mode))
		return true;
	if (IS_NOQUOTA(inode))
		return true;
	if (f2fs_is_atomic_file(inode))
		return true;
	if (fio) {
		if (is_cold_data(fio->page))
			return true;
		if (IS_ATOMIC_WRITTEN_PAGE(fio->page))
			return true;
		if (unlikely(is_sbi_flag_set(sbi, SBI_CP_DISABLED) &&
			f2fs_is_checkpointed_data(sbi, fio->old_blkaddr)))
			return true;
	}
	return false;
}

static inline bool need_inplace_update(struct f2fs_io_info *fio)
{
	struct inode *inode = fio->page->mapping->host;

	if (f2fs_should_update_outplace(inode, fio))
		return false;
#ifdef F2FS_DELTA_COMPRESS
	return false;
#else
	return f2fs_should_update_inplace(inode, fio);
#endif
}

int f2fs_do_write_data_page(struct f2fs_io_info *fio)
{
	struct page *page = fio->page;
	struct inode *inode = page->mapping->host;
	struct dnode_of_data dn;
	struct extent_info ei = {0,0,0};
	struct node_info ni;
	bool ipu_force = false;
	int err = 0;
#ifdef CONFIG_F2FS_BD_STAT
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
#endif
#ifdef F2FS_DELTA_COMPRESS
	int offset[4];
	unsigned int noffset[4];
	int level;

	level = f2fs_delta_get_node_path(inode, page->index, offset, noffset);
	if (level == 0 && offset[0]!=0)
	{			
		f2fs_retrieve_delta(inode, offset[0]);	
	}	
	else if(level>0)
	{
		f2fs_retrieve_inode_delta(inode);	
	}			
#endif
	set_new_dnode(&dn, inode, NULL, NULL, 0);
	if (need_inplace_update(fio) &&
			f2fs_lookup_extent_cache(inode, page->index, &ei)) {
		fio->old_blkaddr = ei.blk + page->index - ei.fofs;

		if (!f2fs_is_valid_blkaddr(fio->sbi, fio->old_blkaddr,
						DATA_GENERIC_ENHANCE))
			return -EFSCORRUPTED;

		ipu_force = true;
		fio->need_lock = LOCK_DONE;
		goto got_it;
	}
	/* Deadlock due to between page->lock and f2fs_lock_op */
	if (fio->need_lock == LOCK_REQ && !f2fs_trylock_op(fio->sbi)){
		return -EAGAIN;
	}
	err = f2fs_get_dnode_of_data(&dn, page->index, LOOKUP_NODE);
	if (err)
		goto out;
	fio->old_blkaddr = dn.data_blkaddr;
	/* This page is already truncated */
	if (fio->old_blkaddr == NULL_ADDR) {
		ClearPageUptodate(page);
		clear_cold_data(page);
		goto out_writepage;
	}
got_it:
	if (__is_valid_data_blkaddr(fio->old_blkaddr) &&
		!f2fs_is_valid_blkaddr(fio->sbi, fio->old_blkaddr,
						DATA_GENERIC_ENHANCE)) {
		printk(KERN_ALERT"invalid blkaddr in do write data page:%d %d %d %d\n",fio->old_blkaddr, page->index, inode->i_ino, dn.ofs_in_node);
		err = -EFSCORRUPTED;
		goto out_writepage;
	}
	/*
	 * If current allocation needs SSR,
	 * it had better in-place writes for updated data.
	 */
	if (ipu_force ||
		(__is_valid_data_blkaddr(fio->old_blkaddr) &&
					need_inplace_update(fio))) {

#ifdef CONFIG_F2FS_BD_STAT
		if (S_ISDIR(inode->i_mode)) {
			bd_lock(sbi);
			bd_inc_array_val(sbi, hotcold_count, HC_REWRITE_HOT_DATA, 1);
			bd_unlock(sbi);
		} else {
			bd_lock(sbi);
			bd_inc_array_val(sbi, hotcold_count, HC_REWRITE_WARM_DATA, 1);
			bd_unlock(sbi);
		}
#endif
		err = f2fs_encrypt_one_page(fio);

		if (err)
			goto out_writepage;

		set_page_writeback(page);
		ClearPageError(page);
		f2fs_put_dnode(&dn);
		if (fio->need_lock == LOCK_REQ)
			f2fs_unlock_op(fio->sbi);
		err = f2fs_inplace_write_data(fio);
		if (err) {
			if (fscrypt_inode_uses_fs_layer_crypto(inode))
				fscrypt_finalize_bounce_page(&fio->encrypted_page);
			if (PageWriteback(page))
				end_page_writeback(page);
		} else {
			set_inode_flag(inode, FI_UPDATE_WRITE);
		}
		trace_f2fs_do_write_data_page(fio->page, IPU);
		return err;
	}

	if (fio->need_lock == LOCK_RETRY) {
		if (!f2fs_trylock_op(fio->sbi)) {
			err = -EAGAIN;
			goto out_writepage;
		}
		fio->need_lock = LOCK_REQ;
	}

	err = f2fs_get_node_info(fio->sbi, dn.nid, &ni);
	if (err)
		goto out_writepage;

	fio->version = ni.version;

	err = f2fs_encrypt_one_page(fio);
	if (err)
		goto out_writepage;

	set_page_writeback(page);
	ClearPageError(page);

	if (fio->compr_blocks && fio->old_blkaddr == COMPRESS_ADDR)
		f2fs_i_compr_blocks_update(inode, fio->compr_blocks - 1, false);

	/* LFS mode write path */
	f2fs_outplace_write_data(&dn, fio);

	trace_f2fs_do_write_data_page(page, OPU);
	set_inode_flag(inode, FI_APPEND_WRITE);
	if (page->index == 0)
		set_inode_flag(inode, FI_FIRST_BLOCK_WRITTEN);
out_writepage:
	f2fs_put_dnode(&dn);
out:
	if (fio->need_lock == LOCK_REQ)
		f2fs_unlock_op(fio->sbi);
	return err;
}

int f2fs_write_single_data_page(struct page *page, int *submitted,
				struct bio **bio,
				sector_t *last_block,
				struct writeback_control *wbc,
				enum iostat_type io_type,
				int compr_blocks)
{
	struct inode *inode = page->mapping->host;
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
	loff_t i_size = i_size_read(inode);
	const pgoff_t end_index = ((unsigned long long)i_size)
							>> PAGE_SHIFT;
	loff_t psize = (loff_t)(page->index + 1) << PAGE_SHIFT;
	unsigned offset = 0;
	bool need_balance_fs = false;
	int err = 0;
	struct f2fs_io_info fio = {
		.sbi = sbi,
		.ino = inode->i_ino,
		.type = DATA,
		.op = REQ_OP_WRITE,
		.op_flags = wbc_to_write_flags(wbc),
		.old_blkaddr = NULL_ADDR,
		.page = page,
		.encrypted_page = NULL,
		.submitted = false,
		.compr_blocks = compr_blocks,
		.need_lock = LOCK_RETRY,
		.io_type = io_type,
		.io_wbc = wbc,
		.bio = bio,
		.last_block = last_block,
	};

	trace_f2fs_writepage(page, DATA);

	/* we should bypass data pages to proceed the kworkder jobs */
	if (unlikely(f2fs_cp_error(sbi))) {
		mapping_set_error(page->mapping, -EIO);
		/*
		 * don't drop any dirty dentry pages for keeping lastest
		 * directory structure.
		 */
		if (S_ISDIR(inode->i_mode))
			goto redirty_out;
		goto out;
	}

	if (unlikely(is_sbi_flag_set(sbi, SBI_POR_DOING)))
		goto redirty_out;

	if (page->index < end_index ||
			f2fs_verity_in_progress(inode) ||
			compr_blocks)
		goto write;

	/*
	 * If the offset is out-of-range of file size,
	 * this page does not have to be written to disk.
	 */
	offset = i_size & (PAGE_SIZE - 1);
	if ((page->index >= end_index + 1) || !offset)
		goto out;

	zero_user_segment(page, offset, PAGE_SIZE);
write:
	if (f2fs_is_drop_cache(inode))
		goto out;
	/* we should not write 0'th page having journal header */
	if (f2fs_is_volatile_file(inode) && (!page->index ||
			(!wbc->for_reclaim &&
			f2fs_available_free_memory(sbi, BASE_CHECK))))
		goto redirty_out;

	/* Dentry blocks are controlled by checkpoint */
	if (S_ISDIR(inode->i_mode)) {
		fio.need_lock = LOCK_DONE;
		err = f2fs_do_write_data_page(&fio);
		goto done;
	}

	if (!wbc->for_reclaim)
		need_balance_fs = true;
	else if (has_not_enough_free_secs(sbi, 0, 0))
		goto redirty_out;
	else
		set_inode_flag(inode, FI_HOT_DATA);

	err = -EAGAIN;
	if (f2fs_has_inline_data(inode)) {
		err = f2fs_write_inline_data(inode, page);
		if (!err)
			goto out;
	}

	if (err == -EAGAIN) {
		err = f2fs_do_write_data_page(&fio);
		if (err == -EAGAIN) {
			fio.need_lock = LOCK_REQ;
			err = f2fs_do_write_data_page(&fio);
		}
	}

	if (err) {
		file_set_keep_isize(inode);
	} else {
		down_write(&F2FS_I(inode)->i_sem);
		if (F2FS_I(inode)->last_disk_size < psize)
			F2FS_I(inode)->last_disk_size = psize;
		up_write(&F2FS_I(inode)->i_sem);
	}

done:
	if (err && err != -ENOENT)
		goto redirty_out;

out:
	inode_dec_dirty_pages(inode);
	if (err) {
		ClearPageUptodate(page);
		clear_cold_data(page);
	}

	if (wbc->for_reclaim) {
		f2fs_submit_merged_write_cond(sbi, NULL, page, 0, DATA);
		clear_inode_flag(inode, FI_HOT_DATA);
		f2fs_remove_dirty_inode(inode);
		submitted = NULL;
	}
	unlock_page(page);
	if (!S_ISDIR(inode->i_mode) && !IS_NOQUOTA(inode) &&
					!F2FS_I(inode)->cp_task)
		f2fs_balance_fs(sbi, need_balance_fs);

	if (unlikely(f2fs_cp_error(sbi))) {
		f2fs_submit_merged_write(sbi, DATA);
		f2fs_submit_merged_ipu_write(sbi, bio, NULL);
		submitted = NULL;
	}

	if (submitted)
		*submitted = fio.submitted ? 1 : 0;

	return 0;

redirty_out:
	redirty_page_for_writepage(wbc, page);
	/*
	 * pageout() in MM traslates EAGAIN, so calls handle_write_error()
	 * -> mapping_set_error() -> set_bit(AS_EIO, ...).
	 * file_write_and_wait_range() will see EIO error, which is critical
	 * to return value of fsync() followed by atomic_write failure to user.
	 */
	if (!err || wbc->for_reclaim)
		return AOP_WRITEPAGE_ACTIVATE;
	unlock_page(page);
	return err;
}

static int f2fs_write_data_page(struct page *page,
					struct writeback_control *wbc)
{
#ifdef CONFIG_F2FS_FS_COMPRESSION
	struct inode *inode = page->mapping->host;

	if (unlikely(f2fs_cp_error(F2FS_I_SB(inode))))
		goto out;

	if (f2fs_compressed_file(inode)) {
		if (f2fs_is_compressed_cluster(inode, page->index)) {
			redirty_page_for_writepage(wbc, page);
			return AOP_WRITEPAGE_ACTIVATE;
		}
	}
out:
#endif

	return f2fs_write_single_data_page(page, NULL, NULL, NULL,
						wbc, FS_DATA_IO, 0);
}

/*
 * This function was copied from write_cche_pages from mm/page-writeback.c.
 * The major change is making write step of cold data page separately from
 * warm/hot data page.
 */
static int f2fs_write_cache_pages(struct address_space *mapping,
					struct writeback_control *wbc,
					enum iostat_type io_type)
{
	int ret = 0;
	int done = 0, retry = 0;
	struct pagevec pvec;
	struct f2fs_sb_info *sbi = F2FS_M_SB(mapping);
	struct bio *bio = NULL;
	sector_t last_block;
#ifdef CONFIG_F2FS_FS_COMPRESSION
	struct inode *inode = mapping->host;
	struct compress_ctx cc = {
		.inode = inode,
		.log_cluster_size = F2FS_I(inode)->i_log_cluster_size,
		.cluster_size = F2FS_I(inode)->i_cluster_size,
		.cluster_idx = NULL_CLUSTER,
		.rpages = NULL,
		.nr_rpages = 0,
		.cpages = NULL,
		.rbuf = NULL,
		.cbuf = NULL,
		.rlen = PAGE_SIZE * F2FS_I(inode)->i_cluster_size,
		.private = NULL,
	};
#endif
	int nr_pages;
	pgoff_t uninitialized_var(writeback_index);
	pgoff_t index;
	pgoff_t end;		/* Inclusive */
	pgoff_t done_index;
	int cycled;
	int range_whole = 0;
	int tag;
	int nwritten = 0;
	int submitted = 0;
	int i;

	pagevec_init(&pvec);

	if (get_dirty_pages(mapping->host) <=
				SM_I(F2FS_M_SB(mapping))->min_hot_blocks)
		set_inode_flag(mapping->host, FI_HOT_DATA);
	else
		clear_inode_flag(mapping->host, FI_HOT_DATA);

	if (wbc->range_cyclic) {
		writeback_index = mapping->writeback_index; /* prev offset */
		index = writeback_index;
		if (index == 0)
			cycled = 1;
		else
			cycled = 0;
		end = -1;
	} else {
		index = wbc->range_start >> PAGE_SHIFT;
		end = wbc->range_end >> PAGE_SHIFT;
		if (wbc->range_start == 0 && wbc->range_end == LLONG_MAX)
			range_whole = 1;
		cycled = 1; /* ignore range_cyclic tests */
	}
	if (wbc->sync_mode == WB_SYNC_ALL || wbc->tagged_writepages)
		tag = PAGECACHE_TAG_TOWRITE;
	else
		tag = PAGECACHE_TAG_DIRTY;
retry:
	retry = 0;
	if (wbc->sync_mode == WB_SYNC_ALL || wbc->tagged_writepages)
		tag_pages_for_writeback(mapping, index, end);
	done_index = index;
	while (!done && !retry && (index <= end)) {
		nr_pages = pagevec_lookup_range_tag(&pvec, mapping, &index, end,
				tag);
		if (nr_pages == 0)
			break;

		for (i = 0; i < nr_pages; i++) {
			struct page *page = pvec.pages[i];
			bool need_readd;
readd:
			need_readd = false;
#ifdef CONFIG_F2FS_FS_COMPRESSION
			if (f2fs_compressed_file(inode)) {
				ret = f2fs_init_compress_ctx(&cc);
				if (ret) {
					done = 1;
					break;
				}

				if (!f2fs_cluster_can_merge_page(&cc,
								page->index)) {
					ret = f2fs_write_multi_pages(&cc,
						&submitted, wbc, io_type);
					if (!ret)
						need_readd = true;
					goto result;
				}

				if (unlikely(f2fs_cp_error(sbi)))
					goto lock_page;

				if (f2fs_cluster_is_empty(&cc)) {
					void *fsdata = NULL;
					struct page *pagep;
					int ret2;

					ret2 = f2fs_prepare_compress_overwrite(
							inode, &pagep,
							page->index, &fsdata);
					if (ret2 < 0) {
						ret = ret2;
						done = 1;
						break;
					} else if (ret2 &&
						!f2fs_compress_write_end(inode,
								fsdata, page->index,
								1)) {
						retry = 1;
						break;
					}
				} else {
					goto lock_page;
				}
			}
#endif
			/* give a priority to WB_SYNC threads */
			if (atomic_read(&sbi->wb_sync_req[DATA]) &&
					wbc->sync_mode == WB_SYNC_NONE) {
				done = 1;
				break;
			}
#ifdef CONFIG_F2FS_FS_COMPRESSION
lock_page:
#endif
			done_index = page->index;
retry_write:
			lock_page(page);

			if (unlikely(page->mapping != mapping)) {
continue_unlock:
				unlock_page(page);
				continue;
			}

			if (!PageDirty(page)) {
				/* someone wrote it for us */
				goto continue_unlock;
			}

			if (PageWriteback(page)) {
				if (wbc->sync_mode != WB_SYNC_NONE)
					f2fs_wait_on_page_writeback(page,
							DATA, true, true);
				else
					goto continue_unlock;
			}

			if (!clear_page_dirty_for_io(page))
				goto continue_unlock;

#ifdef CONFIG_F2FS_FS_COMPRESSION
			if (f2fs_compressed_file(inode)) {
				get_page(page);
				f2fs_compress_ctx_add_page(&cc, page);
				continue;
			}
#endif

			ret = f2fs_write_single_data_page(page, &submitted,
					&bio, &last_block, wbc, io_type, 0);

			if (ret == AOP_WRITEPAGE_ACTIVATE)
				unlock_page(page);
#ifdef CONFIG_F2FS_FS_COMPRESSION
result:
#endif
			nwritten += submitted;
			wbc->nr_to_write -= submitted;

			if (unlikely(ret)) {
				/*
				 * keep nr_to_write, since vfs uses this to
				 * get # of written pages.
				 */
				if (ret == AOP_WRITEPAGE_ACTIVATE) {
					ret = 0;
					goto next;
				} else if (ret == -EAGAIN) {
					ret = 0;
					if (wbc->sync_mode == WB_SYNC_ALL) {
						cond_resched();
						congestion_wait(BLK_RW_ASYNC,
								HZ/50);
						goto retry_write;
					}
					goto next;
				}
				done_index = page->index + 1;
				done = 1;
				break;
			}

			if (wbc->nr_to_write <= 0 &&
					wbc->sync_mode == WB_SYNC_NONE) {
				done = 1;
				break;
			}
next:
			if (need_readd)
				goto readd;
		}
		pagevec_release(&pvec);
		cond_resched();
	}
#ifdef CONFIG_F2FS_FS_COMPRESSION
	/* flush remained pages in compress cluster */
	if (f2fs_compressed_file(inode) && !f2fs_cluster_is_empty(&cc)) {
		ret = f2fs_write_multi_pages(&cc, &submitted, wbc, io_type);
		nwritten += submitted;
		wbc->nr_to_write -= submitted;
		if (ret) {
			done = 1;
			retry = 0;
		}
	}
#endif
	if ((!cycled && !done) || retry) {
		cycled = 1;
		index = 0;
		end = writeback_index - 1;
		goto retry;
	}
	if (wbc->range_cyclic || (range_whole && wbc->nr_to_write > 0))
		mapping->writeback_index = done_index;

	if (nwritten)
		f2fs_submit_merged_write_cond(F2FS_M_SB(mapping), mapping->host,
								NULL, 0, DATA);
	/* submit cached bio of IPU write */
	if (bio)
		f2fs_submit_merged_ipu_write(sbi, &bio, NULL);

	return ret;
}

static inline bool __should_serialize_io(struct inode *inode,
					struct writeback_control *wbc)
{
	if (!S_ISREG(inode->i_mode))
		return false;
	if (f2fs_compressed_file(inode))
		return true;
	if (IS_NOQUOTA(inode))
		return false;
	/* to avoid deadlock in path of data flush */
	if (F2FS_I(inode)->cp_task)
		return false;
	if (wbc->sync_mode != WB_SYNC_ALL)
		return true;
	if (get_dirty_pages(inode) >= SM_I(F2FS_I_SB(inode))->min_seq_blocks)
		return true;
	return false;
}

static int __f2fs_write_data_pages(struct address_space *mapping,
						struct writeback_control *wbc,
						enum iostat_type io_type)
{
	struct inode *inode = mapping->host;
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
	struct blk_plug plug;
	int ret;
	bool locked = false;

	/* deal with chardevs and other special file */
	if (!mapping->a_ops->writepage)
		return 0;

	/* skip writing if there is no dirty page in this inode */
	if (!get_dirty_pages(inode) && wbc->sync_mode == WB_SYNC_NONE)
		return 0;

	/* during POR, we don't need to trigger writepage at all. */
	if (unlikely(is_sbi_flag_set(sbi, SBI_POR_DOING)))
		goto skip_write;

	if ((S_ISDIR(inode->i_mode) || IS_NOQUOTA(inode)) &&
			wbc->sync_mode == WB_SYNC_NONE &&
			get_dirty_pages(inode) < nr_pages_to_skip(sbi, DATA) &&
			f2fs_available_free_memory(sbi, DIRTY_DENTS))
		goto skip_write;

	/* skip writing during file defragment */
	if (is_inode_flag_set(inode, FI_DO_DEFRAG))
		goto skip_write;

	trace_f2fs_writepages(mapping->host, wbc, DATA);

	/* to avoid spliting IOs due to mixed WB_SYNC_ALL and WB_SYNC_NONE */
	if (wbc->sync_mode == WB_SYNC_ALL)
		atomic_inc(&sbi->wb_sync_req[DATA]);
	else if (atomic_read(&sbi->wb_sync_req[DATA]))
		goto skip_write;

	if (__should_serialize_io(inode, wbc)) {
		mutex_lock(&sbi->writepages);
		locked = true;
	}

	blk_start_plug(&plug);
	ret = f2fs_write_cache_pages(mapping, wbc, io_type);
	blk_finish_plug(&plug);

	if (locked)
		mutex_unlock(&sbi->writepages);

	if (wbc->sync_mode == WB_SYNC_ALL)
		atomic_dec(&sbi->wb_sync_req[DATA]);
	/*
	 * if some pages were truncated, we cannot guarantee its mapping->host
	 * to detect pending bios.
	 */

	f2fs_remove_dirty_inode(inode);
	return ret;

skip_write:
	wbc->pages_skipped += get_dirty_pages(inode);
	trace_f2fs_writepages(mapping->host, wbc, DATA);
	return 0;
}

static int f2fs_write_data_pages(struct address_space *mapping,
			    struct writeback_control *wbc)
{
	struct inode *inode = mapping->host;

	return __f2fs_write_data_pages(mapping, wbc,
			F2FS_I(inode)->cp_task == current ?
			FS_CP_DATA_IO : FS_DATA_IO);
}

static void f2fs_write_failed(struct address_space *mapping, loff_t to)
{
	struct inode *inode = mapping->host;
	loff_t i_size = i_size_read(inode);

	if (IS_NOQUOTA(inode))
		return;

	/* In the fs-verity case, f2fs_end_enable_verity() does the truncate */
	if (to > i_size && !f2fs_verity_in_progress(inode)) {
		down_write(&F2FS_I(inode)->i_gc_rwsem[WRITE]);
		down_write(&F2FS_I(inode)->i_mmap_sem);

		truncate_pagecache(inode, i_size);
		f2fs_truncate_blocks(inode, i_size, true);

		up_write(&F2FS_I(inode)->i_mmap_sem);
		up_write(&F2FS_I(inode)->i_gc_rwsem[WRITE]);
	}
}

static int prepare_write_begin(struct f2fs_sb_info *sbi,
			struct page *page, loff_t pos, unsigned len,
			block_t *blk_addr, bool *node_changed)
{
	struct inode *inode = page->mapping->host;
	pgoff_t index = page->index;
	struct dnode_of_data dn;
	struct page *ipage;
	bool locked = false;
	struct extent_info ei = {0,0,0};
	int err = 0;
	int flag;

	/*
	 * we already allocated all the blocks, so we don't need to get
	 * the block addresses when there is no need to fill the page.
	 */
	if (!f2fs_has_inline_data(inode) && len == PAGE_SIZE &&
	    !is_inode_flag_set(inode, FI_NO_PREALLOC) &&
	    !f2fs_verity_in_progress(inode))
		return 0;

	/* f2fs_lock_op avoids race between write CP and convert_inline_page */
	if (f2fs_has_inline_data(inode) && pos + len > MAX_INLINE_DATA(inode))
		flag = F2FS_GET_BLOCK_DEFAULT;
	else
		flag = F2FS_GET_BLOCK_PRE_AIO;

	if (f2fs_has_inline_data(inode) ||
			(pos & PAGE_MASK) >= i_size_read(inode)) {
		__do_map_lock(sbi, flag, true);
		locked = true;
	}

restart:
	/* check inline_data */
	ipage = f2fs_get_node_page(sbi, inode->i_ino);
	if (IS_ERR(ipage)) {
		err = PTR_ERR(ipage);
		goto unlock_out;
	}

	set_new_dnode(&dn, inode, ipage, ipage, 0);

	if (f2fs_has_inline_data(inode)) {
		if (pos + len <= MAX_INLINE_DATA(inode)) {
			f2fs_do_read_inline_data(page, ipage);
			set_inode_flag(inode, FI_DATA_EXIST);
			if (inode->i_nlink)
				set_inline_node(ipage);
		} else {
			err = f2fs_convert_inline_page(&dn, page);
			if (err)
				goto out;
			if (dn.data_blkaddr == NULL_ADDR)
				err = f2fs_get_block(&dn, index);
		}
	} else if (locked) {
		err = f2fs_get_block(&dn, index);
	} else {
		if (f2fs_lookup_extent_cache(inode, index, &ei)) {
			dn.data_blkaddr = ei.blk + index - ei.fofs;
		} else {
			/* hole case */
			err = f2fs_get_dnode_of_data(&dn, index, LOOKUP_NODE);
			if (err || dn.data_blkaddr == NULL_ADDR) {
				f2fs_put_dnode(&dn);
				__do_map_lock(sbi, F2FS_GET_BLOCK_PRE_AIO,
								true);
				WARN_ON(flag != F2FS_GET_BLOCK_PRE_AIO);
				locked = true;
				goto restart;
			}
		}
	}

	/* convert_inline_page can make node_changed */
	*blk_addr = dn.data_blkaddr;
	*node_changed = dn.node_changed;
out:
	f2fs_put_dnode(&dn);
unlock_out:
	if (locked)
		__do_map_lock(sbi, flag, false);
	return err;
}

static int f2fs_write_begin(struct file *file, struct address_space *mapping,
		loff_t pos, unsigned len, unsigned flags,
		struct page **pagep, void **fsdata)
{
	struct inode *inode = mapping->host;
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
	struct page *page = NULL;
	pgoff_t index = ((unsigned long long) pos) >> PAGE_SHIFT;
	bool need_balance = false, drop_atomic = false;
	block_t blkaddr = NULL_ADDR;
	int err = 0;
#ifdef F2FS_DELTA_COMPRESS
	int offset[4];
	unsigned int noffset[4];
	int i,j,level, tmp_loc, end_loc, index1, last_iaddr, cur_size, size_thred=0, compressed_flag=0, delta_num=0, delta_inline_size=0,flag=0;
	unsigned char ff1, ff2, c, ch, ch1;
	char *src_addr=NULL,*dst_addr=NULL, *tp1=NULL, *tp2=NULL,*new_data=NULL, *xor=NULL;		
	void *tp=NULL;
	int ret=0;
	size_t clen;
	struct dnode_of_data dn;
	if(fsdata&&*fsdata!=NULL) *fsdata=NULL;

#endif
	if (trace_android_fs_datawrite_start_enabled()) {
		char *path, pathbuf[MAX_TRACE_PATHBUF_LEN];

		path = android_fstrace_get_pathname(pathbuf,
						    MAX_TRACE_PATHBUF_LEN,
						    inode);
		trace_android_fs_datawrite_start(inode, pos, len,
						 current->pid, path,
						 current->comm);
	}
	trace_f2fs_write_begin(inode, pos, len, flags);
	if (!f2fs_is_checkpoint_ready(sbi)) {
		err = -ENOSPC;
		goto fail;
	}

	if ((f2fs_is_atomic_file(inode) &&
			!f2fs_available_free_memory(sbi, INMEM_PAGES)) ||
			is_inode_flag_set(inode, FI_ATOMIC_REVOKE_REQUEST)) {
		err = -ENOMEM;
		drop_atomic = true;
		goto fail;
	}
	/*
	 * We should check this at this moment to avoid deadlock on inode page
	 * and #0 page. The locking rule for inline_data conversion should be:
	 * lock_page(page #0) -> lock_page(inode_page)
	 */
	if (index != 0) {
		err = f2fs_convert_inline_inode(inode);
		if (err)
			goto fail;
	}

#ifdef F2FS_DELTA_COMPRESS
	level = f2fs_delta_get_node_path(inode, index, offset, noffset);
	if (level == 0 && offset[0]!=0)
	{			
		f2fs_retrieve_delta(inode, offset[0]);	
	}	
	else if(level>0)
	{
		f2fs_retrieve_inode_delta(inode);	
	}			
#endif

repeat:
	/*
	 * Do not use grab_cache_page_write_begin() to avoid deadlock due to
	 * wait_for_stable_page. Will wait that below with our IO control.
	 */
	page = f2fs_pagecache_get_page(mapping, index,
				FGP_LOCK | FGP_WRITE | FGP_CREAT, GFP_NOFS);
	if (!page) {
		err = -ENOMEM;
		goto fail;
	}
	/* TODO: cluster can be compressed due to race with .writepage */

	*pagep = page;

	err = prepare_write_begin(sbi, page, pos, len,
					&blkaddr, &need_balance);
	if (err)
		goto fail;

	if (need_balance && !IS_NOQUOTA(inode) &&
			has_not_enough_free_secs(sbi, 0, 0)) {
		unlock_page(page);
		f2fs_balance_fs(sbi, true);
		lock_page(page);
		if (page->mapping != mapping) {
			/* The page got truncated from under us */
			f2fs_put_page(page, 1);
			goto repeat;
		}
	}
	f2fs_wait_on_page_writeback(page, DATA, false, true);
#ifdef F2FS_DELTA_COMPRESS
	if(is_inode_flag_set(inode, FI_INLINE_DELTA)){
		set_new_dnode(&dn, inode, NULL, NULL, 0);
		err = f2fs_get_dnode_of_data(&dn, page->index, LOOKUP_NODE);
		if (err){
			goto no_comp;		
		}
		dst_addr=kmalloc(PAGE_SIZE, GFP_NOFS);//cp inline to dst addr
		src_addr = inline_data_addr(inode, dn.inode_page);
		memcpy(dst_addr, src_addr, MAX_INLINE_DATA(inode));
		tmp_loc=872*sizeof(__le32)-1;  
		c=dst_addr[tmp_loc];  
		delta_num=c;
		ff1=dst_addr[tmp_loc-1], ff2=dst_addr[tmp_loc-2];
		delta_inline_size=ff2;
		delta_inline_size = (delta_inline_size << BITS_PER_BYTE) | ff1;
		ff1=dst_addr[tmp_loc-3], ff2=dst_addr[tmp_loc-4];
		last_iaddr=ff2;
		last_iaddr = (last_iaddr << BITS_PER_BYTE) | ff1;	
		if(i_size_read(inode)<size_thred && page->index<871&&(inode->i_blocks/4+1)<871){
			last_iaddr = last_iaddr < page->index ? page->index : last_iaddr;
			if(inode->i_blocks % 4 == 0) last_iaddr = last_iaddr < (inode->i_blocks/4) ? (inode->i_blocks/4) : last_iaddr;
			else last_iaddr = last_iaddr < (inode->i_blocks/4+1) ? (inode->i_blocks/4+1) : last_iaddr;
		}
		ff1=last_iaddr, ff2=last_iaddr>>BITS_PER_BYTE;
		dst_addr[tmp_loc-3]=ff1;
		dst_addr[tmp_loc-4]=ff2;
		tmp_loc=872*sizeof(__le32)-6;  
		end_loc=tmp_loc-delta_inline_size;

		for(i=0;i<delta_num;i++){
			ff1=dst_addr[tmp_loc], ff2=dst_addr[tmp_loc-1];
			index1=ff2;
			index1 = (index1 << BITS_PER_BYTE) | ff1;
			c=dst_addr[tmp_loc-2];  
			cur_size=c;
			if(index1==dn.ofs_in_node){
				tp1=kmalloc(cur_size,GFP_NOFS);
				for(j=0;j<cur_size;j++){
					tp1[j]=dst_addr[tmp_loc-sizeof(__le16)-1-j];
				}
				compressed_flag=1;
				break;
			}
			tmp_loc=tmp_loc-sizeof(__le16)-1-cur_size;//2 for index, 1 for size, cursize for delta
		}
no_comp:
		f2fs_put_dnode(&dn);				
	}
	if (len == PAGE_SIZE || PageUptodate(page))
	{
		if(!f2fs_is_atomic_file(inode)){
			if((fsdata)&&*fsdata==NULL && blkaddr!=NEW_ADDR && blkaddr!=NULL_ADDR && PageUptodate(page))/*if base is dirty then we won't perform compress*/
			{
				if(compressed_flag==1)/*delta compressed data*/
				{
					*fsdata=kmalloc(PAGE_SIZE,GFP_NOFS);
					tp=kmap(page);
					new_data=kmalloc(PAGE_SIZE,GFP_NOFS);
					memcpy(new_data,tp,PAGE_SIZE);
					/*decompress delta*/
					if(tp1!=NULL&&cur_size!=0){
						clen=PAGE_SIZE;
						tp2=f2fs_kzalloc(F2FS_I_SB(inode),clen,GFP_NOFS);	
						ret = lzo1x_decompress_safe(tp1, cur_size,
									tp2, &clen);
						if (ret != LZO_E_OK) {
							printk_ratelimited("%sF2FS-fs (%s): lzo decompress failed, ret:%d\n",
									KERN_ERR, F2FS_I_SB(inode)->sb->s_id, ret);
							if(tp1!=NULL) kfree(tp1);
							kfree(new_data);
							kunmap(page);
							kfree(tp2);
							kfree(fsdata);
							goto no_base_out;
						}
						/*retrive base*/
						xor=kmalloc(PAGE_SIZE,GFP_NOFS);
						for(i=0;i<4096;i++){
							ch=new_data[i];
							ch1=tp2[i];
							//creat new page to save ch1 and fill 0 for same
							xor[i]=ch1^ch;
						}
						/*copy to fsdata*/
						memcpy(*fsdata,xor,PAGE_SIZE);
						kfree(tp2);
					}
					kunmap(page);
					kfree(new_data);
				}
				else
				{
					*fsdata=kmalloc(PAGE_SIZE,GFP_NOFS);
					tp=kmap(page);
					memcpy(*fsdata,tp,PAGE_SIZE);
					kunmap(page);	
				}
			}
		}
no_base_out:
		if(tp1!=NULL) kfree(tp1);
		return 0;	
	}
#else
	if (len == PAGE_SIZE || PageUptodate(page))
		return 0;
#endif
	if (!(pos & (PAGE_SIZE - 1)) && (pos + len) >= i_size_read(inode) &&
	    !f2fs_verity_in_progress(inode)) {
		zero_user_segment(page, len, PAGE_SIZE);
		return 0;
	}

	if (blkaddr == NEW_ADDR) {
		zero_user_segment(page, 0, PAGE_SIZE);
		SetPageUptodate(page);
	} else {
		if (!f2fs_is_valid_blkaddr(sbi, blkaddr,
				DATA_GENERIC_ENHANCE_READ)) {
			err = -EFSCORRUPTED;
			goto fail;
		}
#ifdef F2FS_DELTA_COMPRESS
wait_truncate:
		if(is_inode_flag_set(inode, FI_DELTA_TRUNCATING)) {/*to avoid read flash base without delta deleted in retrieve*/
			congestion_wait(BLK_RW_ASYNC, HZ/50);
			if(PageLocked(page)) {
				printk(KERN_ALERT"locked page in f2fs write begin\n");
				f2fs_put_page(page,1);
				flag=1;
			}
			goto wait_truncate;
		}
		if(flag) {
			if(!trylock_page(page)) {
				printk(KERN_ALERT"lock page failed in write begin\n");
				congestion_wait(BLK_RW_ASYNC, HZ/50);
				goto wait_truncate;
			}
		}
#endif
		err = f2fs_submit_page_read(inode, page, blkaddr);
		if (err)
			goto fail;

		lock_page(page);
		if (unlikely(page->mapping != mapping)) {
			f2fs_put_page(page, 1);
			goto repeat;
		}
		if (unlikely(!PageUptodate(page))) {
			err = -EIO;
			goto fail;
		}
#ifdef F2FS_DELTA_COMPRESS
		if(fsdata&&*fsdata==NULL){
			if (!f2fs_is_atomic_file(inode)){
				*fsdata=kmalloc(PAGE_SIZE,GFP_NOFS);
				tp=kmap(page);
				memcpy(*fsdata,tp,PAGE_SIZE);
				kunmap(page);
			}
			f2fs_decompress_delta(page);
#ifdef F2FS_MAIN_COMPRESS
			if(is_inode_flag_set(inode, FI_MAIN_DELTA)){
				f2fs_decompress_main(page);
			}
#endif
		}
#endif
	}
#ifdef F2FS_DELTA_COMPRESS
	if(tp1!=NULL) kfree(tp1);
#endif
	return 0;

fail:
#ifdef F2FS_DELTA_COMPRESS
	if(tp1!=NULL) kfree(tp1);
#endif
	f2fs_put_page(page, 1);
	f2fs_write_failed(mapping, pos + len);
	if (drop_atomic)
		f2fs_drop_inmem_pages_all(sbi, false);
	return err;
}

#ifdef F2FS_MAIN_COMPRESS
/*****************main area delta compress***********************/
bool f2fs_decompress_main(struct page *page)
{	
	int i,j,k,compact_page_num,next_loc,next_loc1,tmp_loc1,delta_loc,delta_num_in_cpage,delta_size,target_loc,free_space_in_cpage,err=0;
	char *meta_addr=NULL, *cpage_addr=NULL, *tp=NULL, *tp1=NULL, *tp2=NULL;
	unsigned char c, ff1,ff2,ff3,ff4,ff5,ff6,ff7,ff8,ff9,ff10,ff11,ff12,ff13;
	block_t delta_index;
	pgoff_t cpage_index;
	struct page *meta_page=NULL;
	struct page *cpage=NULL;
	struct inode *inode=page->mapping->host;
	struct inode *new_inode;
	struct super_block *sb=F2FS_I_SB(inode)->sb;
	if(!inode || inode==NULL) return 0;
	
	new_inode=f2fs_iget(sb, F2FS_I(inode)->meta_id);
	if (IS_ERR(new_inode) || is_bad_inode(new_inode)) {
		set_sbi_flag(F2FS_I_SB(inode), SBI_NEED_FSCK);
		printk(KERN_ALERT"bad inode in decompress main:%d\n", new_inode->i_ino);
		return 0;
	}
	meta_page = f2fs_read_page_for_main_compress(new_inode, 0);
	if (!meta_page) {
		printk(KERN_ALERT"get meta page failed:%d\n",F2FS_I(inode)->meta_id);
		return 0;
	}
	meta_addr=kmalloc(PAGE_SIZE,GFP_NOFS);
	tp=kmap(meta_page);
	memcpy(meta_addr,tp,PAGE_SIZE);
	kunmap(meta_page);
	f2fs_put_page(meta_page,1);
	compact_page_num=F2FS_I(inode)->cpage_num;
	next_loc=0;
	for(i=0;i<compact_page_num;i++){//for each compact page
		ff1=meta_addr[next_loc];
		delta_num_in_cpage=ff1;
		ff2=meta_addr[next_loc+1];
		ff3=meta_addr[next_loc+2];
		free_space_in_cpage=ff3;
		free_space_in_cpage= (free_space_in_cpage << BITS_PER_BYTE) | ff2;
		ff7=meta_addr[next_loc+6];
		ff6=meta_addr[next_loc+5];
		ff5=meta_addr[next_loc+4];
		ff4=meta_addr[next_loc+3];
		cpage_index=ff7;
		cpage_index=(cpage_index<< BITS_PER_BYTE) | ff6;
		cpage_index=(cpage_index<< BITS_PER_BYTE) | ff5;
		cpage_index=(cpage_index<< BITS_PER_BYTE) | ff4;
		tmp_loc1=next_loc+7;
		for(j=0;j<delta_num_in_cpage;j++){//for each delta
			ff11=meta_addr[tmp_loc1+3];
			ff10=meta_addr[tmp_loc1+2];
			ff9=meta_addr[tmp_loc1+1];
			ff8=meta_addr[tmp_loc1];
			delta_index=ff11;
			delta_index=(delta_index<< BITS_PER_BYTE) | ff10;
			delta_index=(delta_index<< BITS_PER_BYTE) | ff9;
			delta_index=(delta_index<< BITS_PER_BYTE) | ff8;
			if(delta_index==page->index){//del current delta
				cpage=f2fs_read_page_for_main_compress(new_inode, j+1);
				if (!cpage) {
					printk(KERN_ALERT"get cpage failed:%d\n",j+1);
					return 0;
				}

				cpage_addr=kmalloc(PAGE_SIZE,GFP_NOFS);
				tp1=kmap(cpage);
				memcpy(cpage_addr,tp1,PAGE_SIZE);
				kunmap(cpage);
				f2fs_put_page(cpage,1);					
				for(k=0;k<j;k++){
					ff12=cpage_addr[next_loc1];
					ff13=cpage_addr[next_loc1+1];
					delta_size=ff13;
					delta_size=(delta_size << BITS_PER_BYTE) | ff12;
					if(k==j) target_loc=next_loc1;
					next_loc1=next_loc1+2+delta_size;						
				}
				tp2=kmalloc(delta_size,GFP_NOFS);
				for(k=0;k<delta_size;k++) tp2[k]=cpage_addr[delta_loc+k];
				f2fs_decompress_delta_for_retrieve(page, tp2, delta_size);
				kfree(cpage_addr);
				goto out;
			}
			tmp_loc1=tmp_loc1+4;
		}
		next_loc=next_loc+2+1+4+4*delta_num_in_cpage;
	}
out:	
	kfree(meta_addr);
	return 1;
}

bool f2fs_store_delta_in_main(struct inode *inode, char *cbuf, int clen, block_t index, int type)
{
	double min_dist=1000000.0;
	int label=0;
	int i,j,k,compact_page_num=0, insert_flag=0;
	unsigned char c,ff1,ff2,ff3,ff4,ff5,ff6,ff7,ff8,ff9,ff10,ff11,ff12,ff13;
	void *tp=NULL, *tp1=NULL;
	char *meta_addr=NULL, *cpage_addr=NULL;
	int delta_num_in_cpage=0,free_space_in_cpage=0, delta_size=0,todelta_size=0;
	block_t delta_index;
	nid_t cpage_index;
	int offset[4];
	unsigned int noffset[4];
	int level=0, err=0;
	int next_loc=0,next_loc1=0, target_loc=0, tmp_loc1=0, contend_flag=0;
	int tmp_ino=-1;
	struct page *meta_page=NULL, *cpage=NULL, *basepage=NULL;
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
	struct super_block *sb = F2FS_I_SB(inode)->sb;
	struct inode *new_inode1=NULL, *tmp_inode=NULL;
	struct dnode_of_data *dn;
	struct bgres_centroid *centroid=NULL;
	
	if(type==0){
	/*hcluster, calc dist to centroid*/	
		double dist1=int_sqrt((inode->i_write_time-sbi->cx1)*(inode->i_write_time-sbi->cx1)+(inode->i_read_time-sbi->cy1)*(inode->i_read_time-sbi->cy1));
		double dist2=int_sqrt((inode->i_write_time-sbi->cx2)*(inode->i_write_time-sbi->cx2)+(inode->i_read_time-sbi->cy2)*(inode->i_read_time-sbi->cy2));
		double dist3=int_sqrt((inode->i_write_time-sbi->cx3)*(inode->i_write_time-sbi->cx3)+(inode->i_read_time-sbi->cy3)*(inode->i_read_time-sbi->cy3));
		double dist4=int_sqrt((inode->i_write_time-sbi->cx4)*(inode->i_write_time-sbi->cx4)+(inode->i_read_time-sbi->cy4)*(inode->i_read_time-sbi->cy4));
		if(min_dist>dist1) {//read cold write cold
			min_dist=dist1;
			label=1;
		}
		if(min_dist>dist2) {//read cold write hot
			min_dist=dist2;
			label=2;
		}
		if(min_dist>dist3) {//read hot write cold
			min_dist=dist3;
			label=3;
		}
		if(min_dist>dist4) {//red hot write hot
			min_dist=dist4;
			label=4;
		}
		if(label!=2) return 0;
	}
	/*find the meta-block*/
	/*****************meta block layout**************************************/
	/*1byte delta num in first cpage CN || 2byte free space in first cpage FS || 4byte index of first cpage PI || 4byte delta1 index....*/ 
	/*cpage layout*/
	/*2byte delta size || delta || ...*/
	if(is_inode_flag_set(inode, FI_MAIN_DELTA)){
		new_inode1=f2fs_iget(sb, F2FS_I(inode)->meta_id);
		if (IS_ERR(new_inode1) || is_bad_inode(new_inode1) || new_inode1==NULL) {
			clear_inode_flag(inode, FI_MAIN_DELTA);
			F2FS_I(inode)->meta_id=-1;
			F2FS_I(inode)->cpage_num=0;
			goto no_maincomp_inode;
		}
		meta_page = f2fs_read_page_for_main_compress(new_inode1, 0);
		if (!meta_page) {
			printk(KERN_ALERT"get meta page failed:%d\n",F2FS_I(inode)->meta_id);
			return 0;
		}
		wait_on_page_writeback(meta_page);
		meta_addr=kmalloc(PAGE_SIZE,GFP_NOFS);
		tp=kmap(meta_page);
		memcpy(meta_addr,tp,PAGE_SIZE);
		compact_page_num=F2FS_I(inode)->cpage_num;
		next_loc=0;
		for(i=0;i<compact_page_num;i++){//for each compact page
			ff1=meta_addr[next_loc];
			delta_num_in_cpage=ff1;
			ff2=meta_addr[next_loc+1];
			ff3=meta_addr[next_loc+2];
			free_space_in_cpage=ff3;
			free_space_in_cpage= (free_space_in_cpage << BITS_PER_BYTE) | ff2;
			ff7=meta_addr[next_loc+6];
			ff6=meta_addr[next_loc+5];
			ff5=meta_addr[next_loc+4];
			ff4=meta_addr[next_loc+3];
			cpage_index=ff7;
			cpage_index=(cpage_index<< BITS_PER_BYTE) | ff6;
			cpage_index=(cpage_index<< BITS_PER_BYTE) | ff5;
			cpage_index=(cpage_index<< BITS_PER_BYTE) | ff4;
			tmp_loc1=next_loc+7;
			for(j=0;j<delta_num_in_cpage;j++){//for each delta
				ff11=meta_addr[tmp_loc1+3];
				ff10=meta_addr[tmp_loc1+2];
				ff9=meta_addr[tmp_loc1+1];
				ff8=meta_addr[tmp_loc1];
				delta_index=ff11;
				delta_index=(delta_index<< BITS_PER_BYTE) | ff10;
				delta_index=(delta_index<< BITS_PER_BYTE) | ff9;
				delta_index=(delta_index<< BITS_PER_BYTE) | ff8;
				if(delta_index==index){//del current delta
					cpage=f2fs_read_page_for_main_compress(new_inode1, cpage_index);
					if(cpage==NULL){
						printk(KERN_ALERT"read cpage fail\n");
						return 0;
					}
					wait_on_page_writeback(cpage);
					cpage_addr=kmalloc(PAGE_SIZE,GFP_NOFS);
					tp1=kmap(cpage);
					memcpy(cpage_addr,tp1,PAGE_SIZE);
					
					next_loc1=0;				
					for(k=0;k<j;k++){
						ff12=cpage_addr[next_loc1];
						ff13=cpage_addr[next_loc1+1];
						delta_size=ff13;
						delta_size=(delta_size << BITS_PER_BYTE) | ff12;
						next_loc1=next_loc1+2+delta_size;						
					}
					ff12=cpage_addr[next_loc1];
					ff13=cpage_addr[next_loc1+1];
					delta_size=ff13;
					delta_size=(delta_size << BITS_PER_BYTE) | ff12;
					for(k=next_loc1;k<(PAGE_SIZE-delta_size-2);k++) cpage_addr[k]=cpage_addr[k+delta_size+2];//del delta
					memcpy(tp1,cpage_addr,PAGE_SIZE);
					kunmap(cpage);
					kfree(cpage_addr);
					if (!PageUptodate(cpage)) SetPageUptodate(cpage);
					if(PageLocked(cpage)) f2fs_put_page(cpage,1);
					else put_page(cpage);
					delta_num_in_cpage=delta_num_in_cpage-1;//update delta num in cpage
					ff1=delta_num_in_cpage;
					meta_addr[next_loc]=ff1;
					free_space_in_cpage+=(delta_size+2);	
					ff2=free_space_in_cpage;
					ff3=free_space_in_cpage >> BITS_PER_BYTE;
					meta_addr[next_loc+1]=ff2;
					meta_addr[next_loc+2]=ff3;//update free space in cpage
					for(k=tmp_loc1;k<PAGE_SIZE-4;k++) meta_addr[k]=meta_addr[k+4];//del delta index
					if(free_space_in_cpage==PAGE_SIZE || delta_num_in_cpage==0){
						for(k=next_loc;k<PAGE_SIZE-7;k++) meta_addr[k]=meta_addr[k+7];
						compact_page_num--;
						F2FS_I(inode)->cpage_num=compact_page_num;
						if(compact_page_num==0){
							clear_inode_flag(inode, FI_MAIN_DELTA);
							zero_user_segment(meta_page, 0, PAGE_SIZE);
							for(k=0;k<PAGE_SIZE;k++) meta_addr[k]=0;
						}
					}
#ifdef F2FS_MAIN_BGRES
					F2FS_I(new_inode1)->centroid->main_compress_num--;
#endif
					goto insert_delta;
				}
				tmp_loc1=tmp_loc1+4;
			}
			next_loc=next_loc+2+1+4+4*delta_num_in_cpage;
		}
insert_delta:
		next_loc=0;
		for(i=0;i<F2FS_I(inode)->cpage_num;i++){//for each compact page
			ff1=meta_addr[next_loc];
			delta_num_in_cpage=ff1;
			ff2=meta_addr[next_loc+1];
			ff3=meta_addr[next_loc+2];
			free_space_in_cpage=ff3;
			free_space_in_cpage= (free_space_in_cpage << BITS_PER_BYTE) | ff2;
			if(free_space_in_cpage>clen+2){
				ff7=meta_addr[next_loc+6];
				ff6=meta_addr[next_loc+5];
				ff5=meta_addr[next_loc+4];
				ff4=meta_addr[next_loc+3];
				cpage_index=ff7;
				cpage_index=(cpage_index<< BITS_PER_BYTE) | ff6;
				cpage_index=(cpage_index<< BITS_PER_BYTE) | ff5;
				cpage_index=(cpage_index<< BITS_PER_BYTE) | ff4;
				cpage=f2fs_read_page_for_main_compress(new_inode1, cpage_index);
				if(cpage==NULL){
					printk(KERN_ALERT"read cpage fail\n");
					return 0;
				}
				wait_on_page_writeback(cpage);
				cpage_addr=kmalloc(PAGE_SIZE,GFP_NOFS);
				tp1=kmap(cpage);
				memcpy(cpage_addr,tp1,PAGE_SIZE);
				next_loc1=0;
				for(j=0;j<delta_num_in_cpage;j++){//for each delta
					ff12=cpage_addr[next_loc1];
					ff13=cpage_addr[next_loc1+1];
					delta_size=ff13;
					delta_size=(delta_size << BITS_PER_BYTE) | ff12;
					next_loc1=next_loc1+2+delta_size;
				}
				ff8=clen;
				ff9=clen>>BITS_PER_BYTE;
				cpage_addr[next_loc1]=ff8;//insert size
				cpage_addr[next_loc1+1]=ff9;
				for(j=0;j<clen;j++) {
					cpage_addr[j+next_loc1+2]=cbuf[j];//insert delta
				}
				tmp_loc1=next_loc+2+1+4+4*delta_num_in_cpage;
				for(j=PAGE_SIZE-1;j>tmp_loc1+3;j--) meta_addr[j]=meta_addr[j-4];
				u32 index2=index;
				ff4=index2;
				ff5=index2>>BITS_PER_BYTE;
				ff6=index2>>(BITS_PER_BYTE*2);
				ff7=index2>>(BITS_PER_BYTE*3);
				meta_addr[tmp_loc1]=ff4;
				meta_addr[tmp_loc1+1]=ff5;
				meta_addr[tmp_loc1+2]=ff6;
				meta_addr[tmp_loc1+3]=ff7;//insert delta index
				delta_num_in_cpage++;
				ff1=delta_num_in_cpage;
				meta_addr[next_loc]=ff1;//update delta num in cpage
				free_space_in_cpage-=(clen+2);//update free space in cpage//need update delta index
				ff2=free_space_in_cpage;
				ff3=free_space_in_cpage>>BITS_PER_BYTE;
				meta_addr[next_loc+1]=ff2;
				meta_addr[next_loc+2]=ff3;				
				insert_flag=1;
				memcpy(tp1,cpage_addr,PAGE_SIZE);
				kunmap(cpage);
				kfree(cpage_addr);
				if (!PageUptodate(cpage)) SetPageUptodate(cpage);
				if(PageLocked(cpage)) f2fs_put_page(cpage,1);
				else put_page(cpage);
				if(!is_inode_flag_set(inode, FI_MAIN_DELTA))	set_inode_flag(inode, FI_MAIN_DELTA);
#ifdef F2FS_MAIN_BGRES
				F2FS_I(new_inode1)->centroid->main_compress_num++;
#endif
				break;
			}
			next_loc=next_loc+2+1+4+4*delta_num_in_cpage;
		}		
		kunmap(meta_page);
		if (!PageUptodate(meta_page)) SetPageUptodate(meta_page);
		kfree(meta_addr);
		if(PageLocked(meta_page)) f2fs_put_page(meta_page,1);
		else put_page(meta_page);
	}
	if(insert_flag==0)
	{
no_maincomp_inode:
		if(!is_inode_flag_set(inode, FI_MAIN_DELTA))
		{
			new_inode1 = f2fs_new_inode(inode, S_ISGID);
			if (IS_ERR(new_inode1))
				return PTR_ERR(new_inode1);
			new_inode1->i_op = &f2fs_file_inode_operations;
			new_inode1->i_fop = &f2fs_file_operations;
			if(new_inode1->i_mapping==NULL) printk(KERN_ALERT"null mapping in main compress:%d\n", new_inode1->i_mapping);
			new_inode1->i_mapping->a_ops = &f2fs_dblock_aops;
			f2fs_lock_op(sbi);
			err = f2fs_acquire_orphan_inode(sbi);
			if (err)
				return err;
			err = f2fs_do_tmpfile(new_inode1, inode);
			if (err)
				return err;
			f2fs_add_orphan_inode(new_inode1);
			f2fs_alloc_nid_done(sbi, new_inode1->i_ino);
			f2fs_unlock_op(sbi);
			unlock_new_inode(new_inode1);
			//f2fs_balance_fs(sbi, true);	
#ifdef F2FS_MAIN_BGRES
			sbi->bgres_lock=1;
			spin_lock(&sbi->bgres_list_lock);
			F2FS_I(new_inode1)->centroid->ino=new_inode1->i_ino;
			F2FS_I(new_inode1)->centroid->i_read_time=inode->i_read_time;
			F2FS_I(new_inode1)->centroid->i_write_time=inode->i_write_time;
			F2FS_I(new_inode1)->ori_ino=inode->i_ino;
			F2FS_I(new_inode1)->cpage_num=F2FS_I(inode)->cpage_num;
			if(sbi->first_ino<0 || f2fs_check_nid_range(sbi, sbi->first_ino)) {
				sbi->first_ino=new_inode1->i_ino;
			}
			else
			{
				tmp_ino=sbi->first_ino;
				while(tmp_ino>=0)
				{	
					tmp_inode=f2fs_iget(sb, tmp_ino);
					if (IS_ERR(tmp_inode) || is_bad_inode(tmp_inode) || tmp_inode==NULL) {
						printk(KERN_ALERT"read tail main compress inode failed:%d\n", tmp_ino);
						return 0;
					}	
					tmp_ino=F2FS_I(tmp_inode)->next_ino;			
				}	
				F2FS_I(tmp_inode)->next_ino=new_inode1->i_ino;
			}
			list_add_tail(&F2FS_I(new_inode1)->centroid->bgres_inode_list, &sbi->bgres_list);
			spin_unlock(&sbi->bgres_list_lock);
			sbi->bgres_lock=0;
#endif
			F2FS_I(inode)->meta_id=new_inode1->i_ino;
			//alloc page alloc block
			meta_page = __page_cache_alloc(GFP_NOFS);
			if (!meta_page)
				return 0;
			meta_page->index=0;
			meta_page->mapping=new_inode1->i_mapping;
repeat:
			err = add_to_page_cache_lru(meta_page, new_inode1->i_mapping, 0, GFP_NOFS);
			if (unlikely(err)) {
				put_page(meta_page);
				meta_page = NULL;
				if (err == -EEXIST)
					goto repeat;
			}
			zero_user_segment(meta_page, 0, PAGE_SIZE);
			set_inode_flag(inode, FI_MAIN_DELTA);
		}
		else
		{
			if(new_inode1==NULL) {
				new_inode1=f2fs_iget(sb,F2FS_I(inode)->meta_id);
				if (IS_ERR(new_inode1) || is_bad_inode(new_inode1)) {
					set_sbi_flag(sbi, SBI_NEED_FSCK);
					printk(KERN_ALERT"bad inode in main compress1:%d\n", new_inode1->i_ino);
					return 0;
				}
			}
			meta_page=f2fs_read_page_for_main_compress(new_inode1, 0);
			if(meta_page==NULL) {
				printk(KERN_ALERT"read meta page failed\n");
				return 0;
			}
			wait_on_page_writeback(meta_page);	
		}
		if (!PageUptodate(meta_page)) SetPageUptodate(meta_page);	
		meta_addr=kmalloc(PAGE_SIZE,GFP_NOFS);
		tp=kmap(meta_page);
		memcpy(meta_addr,tp,PAGE_SIZE);
		compact_page_num=F2FS_I(inode)->cpage_num;	
		if(compact_page_num>255){
			kunmap(meta_page);
			kfree(meta_addr);
			if(PageLocked(meta_page)) f2fs_put_page(meta_page,1);
			else put_page(meta_page);
			goto writeback;	
		}	
		F2FS_I(inode)->cpage_num++;
		kunmap(meta_page);
		if(PageLocked(meta_page)) f2fs_put_page(meta_page,1);
		else put_page(meta_page);
repeat1:
		cpage = __page_cache_alloc(GFP_NOFS);
		if (!cpage)
			return NULL;
		cpage->mapping=new_inode1->i_mapping;
		cpage->index=compact_page_num+1;
		err = add_to_page_cache_lru(cpage, new_inode1->i_mapping, compact_page_num+1, GFP_NOFS);
		if (unlikely(err)) {
			put_page(cpage);
			cpage = NULL;
			if (err == -EEXIST)
				goto repeat1;
		}	
		zero_user_segment(cpage, 0, PAGE_SIZE);
		tp1=kmap(cpage);
		cpage_addr=kmalloc(PAGE_SIZE,GFP_NOFS);
		memcpy(cpage_addr,tp1,PAGE_SIZE);
		kunmap(cpage);
		if (!PageUptodate(cpage)) SetPageUptodate(cpage);
		if(PageLocked(cpage)) f2fs_put_page(cpage,1);
		else put_page(cpage);
		ff1=clen;
		ff2=clen>>BITS_PER_BYTE;
		cpage_addr[0]=ff1;//insert size
		cpage_addr[1]=ff2;
		for(i=0;i<clen;i++) cpage_addr[i+2]=cbuf[i];//insert delta
		next_loc=0;
		for(i=0;i<compact_page_num;i++){
			ff1=meta_addr[next_loc];
			delta_num_in_cpage=ff1;
			next_loc=next_loc+2+1+4+4*delta_num_in_cpage;
		}
		delta_num_in_cpage=1;
		ff1=delta_num_in_cpage;
		meta_addr[next_loc]=ff1;//update delta number in cpage
		free_space_in_cpage=PAGE_SIZE-(clen+2);//update free space in cpage
		ff2=free_space_in_cpage;
		ff3=free_space_in_cpage>>BITS_PER_BYTE;
		meta_addr[next_loc+1]=ff2;
		meta_addr[next_loc+2]=ff3;
		u32 cpage_index1=cpage->index;
		ff8=cpage_index1;
		ff9=cpage_index1>>BITS_PER_BYTE;
		ff10=cpage_index1>>(BITS_PER_BYTE*2);
		ff11=cpage_index1>>(BITS_PER_BYTE*3);
		meta_addr[next_loc+3]=ff8;
		meta_addr[next_loc+4]=ff9;
		meta_addr[next_loc+5]=ff10;
		meta_addr[next_loc+6]=ff11;	//update cpage index		
		u32 index1=index;
		ff4=index1;//update delta index
		ff5=index1>>BITS_PER_BYTE;
		ff6=index1>>(BITS_PER_BYTE*2);
		ff7=index1>>(BITS_PER_BYTE*3);
		meta_addr[next_loc+7]=ff4;
		meta_addr[next_loc+8]=ff5;
		meta_addr[next_loc+9]=ff6;
		meta_addr[next_loc+10]=ff7;
		compact_page_num++;
		F2FS_I(inode)->cpage_num=compact_page_num;
		meta_page=f2fs_read_page_for_main_compress(new_inode1, 0);
		if(meta_page==NULL) {
			printk(KERN_ALERT"read meta page failed\n");
			return 0;
		}
		tp=kmap(meta_page);
		memcpy(tp, meta_addr,PAGE_SIZE);
		kunmap(meta_page);
		kfree(meta_addr);
		if (!PageUptodate(meta_page)) SetPageUptodate(meta_page);
		if(PageLocked(meta_page)) f2fs_put_page(meta_page,1);
		else put_page(meta_page);
		cpage=f2fs_read_page_for_main_compress(new_inode1, compact_page_num);
		if(cpage==NULL) {
			printk(KERN_ALERT"read c page failed\n");
			return 0;
		}		
		tp1=kmap(cpage);
		memcpy(tp1,cpage_addr,PAGE_SIZE);
		kunmap(cpage);
		kfree(cpage_addr);
		if (!PageUptodate(cpage)) SetPageUptodate(cpage);
		if(PageLocked(cpage)) f2fs_put_page(cpage,1);
		else put_page(cpage);
#ifdef F2FS_MAIN_BGRES
		F2FS_I(new_inode1)->centroid->main_compress_num++;
#endif
	}
	
writeback:
	meta_page= f2fs_read_page_for_main_compress(new_inode1, 0);
	if(meta_page==NULL) {
		printk(KERN_ALERT"read meta page failed\n");
		return 0;
	}
	tp=kmap(meta_page);
	meta_addr=kmalloc(PAGE_SIZE,GFP_NOFS);
	memcpy(meta_addr,tp,PAGE_SIZE);
	if(PageDirty(meta_page)){
		set_new_dnode(dn, new_inode1, NULL, NULL, 0);
		err = f2fs_get_dnode_of_data(dn, 0, LOOKUP_NODE);
		if (err)
			return 0;
		err=f2fs_convert_inline_delta(dn, meta_page);
		if(err){
			printk(KERN_ALERT"unlock metapage failed in f2fs convert inline delta:%d\n", inode->i_ino);
			f2fs_put_dnode(dn);
			f2fs_put_page(meta_page,1);
			congestion_wait(BLK_RW_ASYNC, HZ/50);
			goto writeback;
		}
		dn->node_changed=true;
		if (!PageUptodate(meta_page)) SetPageUptodate(meta_page);
		f2fs_put_dnode(dn);
	}
	kunmap(meta_page);
	if(PageLocked(meta_page)) f2fs_put_page(meta_page,1);
	else put_page(meta_page);
	next_loc=0;
	for(i=0;i<F2FS_I(inode)->cpage_num;i++){
		ff7=meta_addr[next_loc+6];
		ff6=meta_addr[next_loc+5];
		ff5=meta_addr[next_loc+4];
		ff4=meta_addr[next_loc+3];
		cpage_index=ff7;
		cpage_index=(cpage_index<< BITS_PER_BYTE) | ff6;
		cpage_index=(cpage_index<< BITS_PER_BYTE) | ff5;
		cpage_index=(cpage_index<< BITS_PER_BYTE) | ff4;
writeback1:
		cpage=f2fs_read_page_for_main_compress(new_inode1, i+1);
		ff1=meta_addr[next_loc];
		delta_num_in_cpage=ff1;
		if(cpage==NULL) {
			printk(KERN_ALERT"read cpage failed\n");
			return 0;
		}	
		if(PageDirty(cpage)){
			set_new_dnode(dn, new_inode1, NULL, NULL, 0);
			err = f2fs_get_dnode_of_data(dn, i+1, LOOKUP_NODE);
			if (err)
				return 0;
			err=f2fs_convert_inline_delta(dn, cpage);
			if(err){
				printk(KERN_ALERT"unlock cpage failed in f2fs convert inline delta:%d %d\n", inode->i_ino, cpage->index);
				f2fs_put_dnode(dn);
				f2fs_put_page(cpage,1);
				congestion_wait(BLK_RW_ASYNC, HZ/50);
				goto writeback1;
			}
			dn->node_changed=true;
			if (!PageUptodate(cpage)) SetPageUptodate(cpage);
			f2fs_put_dnode(dn);
		}
		if(PageLocked(cpage)) f2fs_put_page(cpage,1);
		else put_page(cpage);
		next_loc=next_loc+2+1+4+4*delta_num_in_cpage;
	}	
	kfree(meta_addr);
	return 1;	
}

struct page *f2fs_read_page_for_main_compress(struct inode *inode, pgoff_t index)
{
	struct page *page=NULL;
	struct f2fs_node *rn;
	struct page *ipage;
	__le32 *addr_array;
	int base = 0, ret = 0, err = 0;
	block_t blkaddr = NULL_ADDR;
	if(inode==NULL||inode->i_mapping==NULL) return 0;
	page = f2fs_pagecache_get_page(inode->i_mapping, index,
			FGP_LOCK | FGP_WRITE | FGP_CREAT, GFP_NOFS);
	if (!page) {
		err = -ENOMEM;
		printk(KERN_ALERT"get page failed in f2fs_read_page_for_main_compress\n");
		return err;
	}
/*need to read from flash and decompress*/
	if (!PageUptodate(page)) {
		ipage = f2fs_get_node_page(F2FS_I_SB(inode), inode->i_ino);
		if (IS_ERR(ipage)) {
			err = PTR_ERR(ipage);
			f2fs_put_page(page, 1);
			printk(KERN_ALERT"cannot find ipage page in main bgres\n");
			return err;
		}
		rn = F2FS_NODE(ipage);
		if (IS_INODE(ipage) && f2fs_has_extra_attr(inode))
			base = get_extra_isize(inode);
		/* Get physical address of data block */
		addr_array = blkaddr_in_node(rn);
		blkaddr = addr_array[base + index];//problematic
		if (!f2fs_is_valid_blkaddr(F2FS_I_SB(inode), blkaddr,
				DATA_GENERIC_ENHANCE_READ)) {
			err = -EFSCORRUPTED;
			printk(KERN_ALERT"test in read page for main compress7:%d %d\n", inode->i_ino, index);
			goto fail;
		}
		err = f2fs_submit_page_read(inode, page, blkaddr);
		if (err){
			goto fail;	
		}
		SetPageUptodate(page);	
		f2fs_put_page(ipage, 1);	
	}	
/*	
	page = find_get_entry(inode->i_mapping, index);
	if (radix_tree_exceptional_entry(page))
		page = NULL;
	if (!page)
		goto no_page;
		
	if(!PageLocked(page)) lock_page(page);
	if(!PageLocked(page)) {
		printk(KERN_ALERT"unlock page in read page for main:%d %d\n", inode->i_ino,index);
		congestion_wait(BLK_RW_ASYNC, HZ/50);
		goto repeat;
	}
no_page:
	if (!page) {
		int err;
		page = __page_cache_alloc(GFP_NOFS);
		if (!page)
			return NULL;
		err = add_to_page_cache_lru(page, inode->i_mapping, index, GFP_NOFS);
		if (unlikely(err)) {
			put_page(page);
			page = NULL;
			if (err == -EEXIST)
				goto repeat;
		}
	}	
	if (!PageUptodate(page)){
		BUG_ON(!PageLocked(page));
		set_new_dnode(dn, inode, NULL, NULL, 0);
		ret = f2fs_get_dnode_of_data(dn, index,
						LOOKUP_NODE);
		rn = F2FS_NODE(dn->node_page);
		if (IS_INODE(dn->node_page) && f2fs_has_extra_attr(inode))
			base = get_extra_isize(inode);

		addr_array = blkaddr_in_node(rn);
		blkaddr = addr_array[base + dn->ofs_in_node];
		if (!f2fs_is_valid_blkaddr(F2FS_I_SB(inode), blkaddr,
				DATA_GENERIC_ENHANCE_READ)) {
			err = -EFSCORRUPTED;
			printk(KERN_ALERT"test in read page for main compress7:%d %d\n", inode->i_ino, index);
			goto fail;
		}
		err = f2fs_submit_page_read(inode, page, blkaddr);
		if (err){
			goto fail;	
		}
		SetPageUptodate(page);	
		f2fs_put_dnode(dn);
	}*/
	return page;
fail:
	f2fs_put_page(ipage, 1);	
	unlock_page(page);
	printk(KERN_ALERT"get page failed in main compress:%d %d\n", inode->i_ino, index);
	return NULL;
}

#endif
/**********inline node data replacement********************/
bool innode_data_replacement(struct file *file, struct dnode_of_data *dn, int index, char *cbuf, size_t clen, int delta_num, int delta_inline_size, char* src_addr, char *dst_addr)
{
	int i,j, tmp_loc, end_loc, index1, cur_size;
	int max_clen=0;
	int max_cloc=0;
	int max_index=0;
	int err=0, main_cflag=0;
	unsigned char c, ff1, ff2;
	char *rbuf;
	struct inode *inode=dn->inode;
	tmp_loc=872*sizeof(__le32)-6;  
	end_loc=tmp_loc-delta_inline_size;
	for(i=0;i<delta_num;i++){//search for max clen
		ff1=dst_addr[tmp_loc], ff2=dst_addr[tmp_loc-1];
		index1=ff2;
		index1 = (index1 << BITS_PER_BYTE) | ff1;
		c=dst_addr[tmp_loc-2];  
		cur_size=c;
		if(cur_size>max_clen){
			max_clen=cur_size;
			max_cloc=tmp_loc;
			max_index=index1;
		}
		tmp_loc=tmp_loc-sizeof(__le16)-1-cur_size;//2 for index, 1 for size, cursize for delta
	}
	if(clen<max_clen-81)/*replace delta*/
	{
		rbuf=f2fs_kzalloc(F2FS_I_SB(inode),max_clen,GFP_NOFS);
		
		//evict max delta
		for(j=0;j<max_clen;j++) rbuf[j]=dst_addr[max_cloc-j];
		for(j=max_cloc;j>end_loc+sizeof(__le16)+1+cur_size;j--) dst_addr[j]=dst_addr[j-sizeof(__le16)-1-max_clen];
		for(j=end_loc+sizeof(__le16)+1+max_clen;j>end_loc;j--) dst_addr[j]=0;    
		delta_inline_size=delta_inline_size-max_clen-sizeof(__le16)-1;
		ff1=delta_inline_size, ff2=delta_inline_size>>BITS_PER_BYTE;
		dst_addr[872*sizeof(__le32)-2]=ff1;
		dst_addr[872*sizeof(__le32)-3]=ff2;
		end_loc=872*sizeof(__le32)-6-delta_inline_size;
		//insert cur delta
		ff1=dn->ofs_in_node, ff2=dn->ofs_in_node>>BITS_PER_BYTE;
		dst_addr[end_loc]=ff1;
		dst_addr[end_loc-1]=ff2;
		c=clen;
		dst_addr[end_loc-2]=c;
		for(j=0;j<clen;j++) dst_addr[end_loc-j-sizeof(__le16)-1]=cbuf[j];
		delta_inline_size=delta_inline_size+clen+sizeof(__le16)+1;
		ff1=delta_inline_size, ff2=delta_inline_size>>BITS_PER_BYTE;
		dst_addr[872*sizeof(__le32)-2]=ff1;
		dst_addr[872*sizeof(__le32)-3]=ff2;		
		memcpy(src_addr, dst_addr, MAX_INLINE_DATA(dn->inode));
		set_page_dirty(dn->inode_page);	
		dn->node_changed=true;
#ifdef F2FS_MAIN_COMPRESS
		f2fs_put_dnode(dn);
		f2fs_store_delta_in_main(inode,rbuf, max_clen,max_index, 1);//no eviction, turn to main compress
		set_new_dnode(dn, inode, NULL, NULL, 0);
		err = f2fs_get_dnode_of_data(dn, index, LOOKUP_NODE);
		if (err){
			kfree(rbuf);
			printk(KERN_ALERT"get dnode failed in innode replacement\n");
			return err;		
		}
		kfree(rbuf);
		return 0;
#else
wait_unlock1:
		err=f2fs_decomp_evict_delta(dn, rbuf, max_clen, max_index);
		if(err>0) {
			congestion_wait(BLK_RW_ASYNC, HZ/50);
			goto wait_unlock1;
		}
		kfree(rbuf);
		return 0;
#endif	
	}
	return 1;
	
}

bool f2fs_decomp_evict_delta(struct dnode_of_data *dn, char *rbuf, int rlen, int index)
{
	struct page *basepage;
	struct inode *inode=dn->inode;
	struct address_space *mapping = inode->i_mapping;
	struct f2fs_node *rn;
	__le32 *addr_array;
	int base = 0, err=0;
	block_t blkaddr;

	if (!mapping || !mapping->host || !F2FS_I_SB(mapping->host) || !NM_I(F2FS_I_SB(mapping->host)) || !F2FS_I_SB(mapping->host)->mounted) 
	{
		printk(KERN_ALERT"null mapping in retrieve inode\n");
		return false;
	}

	basepage = find_get_entry(inode->i_mapping, index);
	if (radix_tree_exceptional_entry(basepage))
		basepage = NULL;
	if (!basepage){
		basepage = __page_cache_alloc(FGP_WRITE | FGP_CREAT);
		if (!basepage) {
			return -1;//no fs page left, pending for process
		}
	}
	if (!trylock_page(basepage)) {
		put_page(basepage);
		printk(KERN_ALERT"lock base page failed in decompevict delta:%d %d\n", inode->i_ino, index);
		return 1;
	}
	f2fs_lock_op(F2FS_I_SB(inode));
	/*need to read from flash and decompress*/
	if (!PageUptodate(basepage)) {
		/*read base blkaddr*/
		if (IS_INODE(dn->inode_page) && f2fs_has_extra_attr(inode))
			base = get_extra_isize(inode);
		rn = F2FS_NODE(dn->inode_page);
		addr_array = blkaddr_in_node(rn);	
		if (__is_valid_data_blkaddr(addr_array[base+index]) && !f2fs_is_valid_blkaddr(F2FS_I_SB(inode), addr_array[base+index], DATA_GENERIC_ENHANCE)) {
			printk(KERN_ALERT"invalid blkaddr in inode retrieve:%lu %d\n", addr_array[base+index],inode->i_ino);
			f2fs_unlock_op(F2FS_I_SB(inode));
			f2fs_put_page(basepage, 1);	
			return -1;	
		}
		err = f2fs_submit_page_read(inode, basepage, addr_array[base+index]);
		if (err || unlikely(basepage->mapping != inode->i_mapping)) {
			printk(KERN_ALERT"cannot find base page in flash in inode retrieve:%d %d %d\n",inode->i_ino, basepage->index, addr_array[base+index]);
			f2fs_unlock_op(F2FS_I_SB(inode));
			f2fs_put_page(basepage, 1);	
			return -1;
		}
		err=f2fs_decompress_delta_for_retrieve(basepage, rbuf, rlen);
		if (err){
			printk(KERN_ALERT"decompress failed in inode retrieve\n");
			f2fs_unlock_op(F2FS_I_SB(inode));
			if(PageLocked(basepage)) f2fs_put_page(basepage, 1);	
			else put_page(basepage);
			return -1;
		}
		SetPageUptodate(basepage);
	}
	err=f2fs_convert_inline_delta(dn, basepage);/*perform page writeback*/
	if(err) {
		printk(KERN_ALERT"err in convert inline delta:%d %d %d\n", inode->i_ino, current->pid, current->tgid);
		f2fs_unlock_op(F2FS_I_SB(inode));
		if(PageLocked(basepage)) f2fs_put_page(basepage, 1);	
		else put_page(basepage);	
		return -1;
	}	
	f2fs_unlock_op(F2FS_I_SB(inode));
	if(PageLocked(basepage)) f2fs_put_page(basepage, 1);

	f2fs_remove_dirty_inode(inode);
	/* this converted inline_data should be recovered. */
	set_inode_flag(inode, FI_APPEND_WRITE);
	f2fs_balance_fs(F2FS_I_SB(inode), dn->node_changed);
	return 0;
}



/**************************************************/
static int f2fs_write_end(struct file *file,
			struct address_space *mapping,
			loff_t pos, unsigned len, unsigned copied,
			struct page *page, void *fsdata)
{
	struct inode *inode = page->mapping->host;
/*****************revised********************************/
#ifdef F2FS_DELTA_COMPRESS
	char *data, *new_data=NULL, *xor=NULL, *cbuf=NULL, *src_addr=NULL,*dst_addr=NULL;
	void *tp=NULL, *private=NULL;
	unsigned char c, ff1, ff2, ch, ch1;
	size_t rlen, clen;
	unsigned char *ss, *fname;
	int i,j,tmp_loc, end_loc, index, cur_size, next_loc, size_thred, delta_compress_enable=0, left_iaddr=0, delta_flag=0, err=0,ret=0,last_iaddr, delta_num=0, delta_inline_size=0, diff=0, replace_flag=1,main_flag=0;
	struct dnode_of_data dn;
	struct page *ipage, *node_page;
	set_new_dnode(&dn, inode, NULL, NULL, 0);
	err = f2fs_get_dnode_of_data(&dn, page->index, LOOKUP_NODE);
	if (err){
		goto delta_out;		
	}
	ipage=dn.inode_page;
	node_page=dn.node_page;
	if(fsdata&&fsdata!=NULL)
	{
		f2fs_wait_on_page_writeback(dn.inode_page, NODE, true, true);
/*******************************inline area layout*************************
reserved  | data index |   ...stop when meets... | 1B delta sizes| 2B indexes| deltas | 1B delta sizes | 2B indexes | xattr
**********************************************************************************************/
		dst_addr=kmalloc(PAGE_SIZE, GFP_NOFS);//cp inline to dst addr
		src_addr = inline_data_addr(inode, dn.inode_page);
		memcpy(dst_addr, src_addr, MAX_INLINE_DATA(inode));
		/********************************evict old delta****************************/
		//if delta already in inline
		if(is_inode_flag_set(inode, FI_INLINE_DELTA)){
			tmp_loc=872*sizeof(__le32)-1;  
			c=dst_addr[tmp_loc];  
			delta_num=c;
			ff1=dst_addr[tmp_loc-1], ff2=dst_addr[tmp_loc-2];
			delta_inline_size=ff2;
			delta_inline_size = (delta_inline_size << BITS_PER_BYTE) | ff1;
			ff1=dst_addr[tmp_loc-3], ff2=dst_addr[tmp_loc-4];
			last_iaddr=ff2;
			last_iaddr = (last_iaddr << BITS_PER_BYTE) | ff1;	
			if(i_size_read(inode)<size_thred && page->index<871&&(inode->i_blocks/4+1)<871){
				last_iaddr = last_iaddr < page->index ? page->index : last_iaddr;
				if(inode->i_blocks % 4 == 0) last_iaddr = last_iaddr < (inode->i_blocks/4) ? (inode->i_blocks/4) : last_iaddr;
				else last_iaddr = last_iaddr < (inode->i_blocks/4+1) ? (inode->i_blocks/4+1) : last_iaddr;
			}
			ff1=last_iaddr, ff2=last_iaddr>>BITS_PER_BYTE;
			dst_addr[tmp_loc-3]=ff1;
			dst_addr[tmp_loc-4]=ff2;	
			tmp_loc=872*sizeof(__le32)-6;  
			end_loc=tmp_loc-delta_inline_size;
			for(i=0;i<delta_num;i++){
				ff1=dst_addr[tmp_loc], ff2=dst_addr[tmp_loc-1];
				index=ff2;
				index = (index << BITS_PER_BYTE) | ff1;
				c=dst_addr[tmp_loc-2];  
				cur_size=c;
				if(index==dn.ofs_in_node){
					for(j=tmp_loc;j>end_loc+sizeof(__le16)+1+cur_size;j--) dst_addr[j]=dst_addr[j-sizeof(__le16)-1-cur_size];
					for(j=end_loc+sizeof(__le16)+1+cur_size;j>end_loc;j--) dst_addr[j]=0;    
					delta_inline_size=delta_inline_size-cur_size-sizeof(__le16)-1;
					delta_num--;
					c=delta_num;
					dst_addr[872*sizeof(__le32)-1]=c;  
					ff1=delta_inline_size, ff2=delta_inline_size>>BITS_PER_BYTE;
					dst_addr[872*sizeof(__le32)-2]=ff1;
					dst_addr[872*sizeof(__le32)-3]=ff2;
					if(delta_num==0 || delta_inline_size==0){
						dst_addr[872*sizeof(__le32)-1]=0;
						dst_addr[872*sizeof(__le32)-2]=0;
						dst_addr[872*sizeof(__le32)-3]=0;						
						dst_addr[872*sizeof(__le32)-4]=0;
						dst_addr[872*sizeof(__le32)-5]=0;
					}
					memcpy(src_addr, dst_addr, MAX_INLINE_DATA(inode));
					set_page_dirty(dn.inode_page);
					break;
				}
				tmp_loc=tmp_loc-sizeof(__le16)-1-cur_size;//2 for index, 1 for size, cursize for delta
			}				
			if(delta_num==0) {
				clear_inode_flag(inode, FI_INLINE_DELTA);
				F2FS_I(inode)->i_flags &= ~F2FS_DELTA_INLINE;
			}
		}
		if(!PageDirty(page)) f2fs_bug_on(F2FS_I_SB(inode), dn.data_blkaddr==NEW_ADDR);
		if(PageDirty(page)) {/*we dont perform compress on dirty page*///problematic
			kfree(fsdata);
			kfree(dst_addr);
			f2fs_put_dnode(&dn);
			goto delta_out;
		}
		/*calc xor*/
		data=(char *)fsdata;
		new_data=kmalloc(PAGE_SIZE,GFP_NOFS);
		tp=kmap(page);
		memcpy(new_data,tp,PAGE_SIZE);
		xor=kmalloc(PAGE_SIZE,GFP_NOFS);
		for(i=0;i<4096;i++){
			ch=data[i];
			ch1=new_data[i];
				//creat new page to save ch1 and fill 0 for same
			xor[i]=ch1^ch;
		}
		/*compress xor*/
		rlen=PAGE_SIZE;
		clen=lzo1x_worst_compress(rlen);
		cbuf=f2fs_kzalloc(F2FS_I_SB(inode),clen,GFP_NOFS);
		private=f2fs_kvmalloc(F2FS_I_SB(inode),LZO1X_MEM_COMPRESS,GFP_NOFS);
		ret=lzo1x_1_compress(xor,rlen,cbuf,&clen,private);
		if(ret!=0)
		{
			printk_ratelimited("%sF2FS-fs (%s): lzo compress failed, ret:%d\n", KERN_ERR, F2FS_I_SB(inode)->sb->s_id,ret);
			return -EIO;
		}
		kfree(private);
		/******************************check if free space is enough to accommodate delta*************************************/
		//calc left free space 
		size_thred = 852*PAGE_SIZE;//20 offsets for delta // 
		if(file && file->f_path.dentry && file->f_path.dentry->d_name.name){
			if((i_size_read(inode)<size_thred)&&!is_inode_flag_set(inode, FI_FINISH_TRUNCATE))// && strstr(file->f_path.dentry->d_name.name,ss)!=NULL)
			{
				if(dn.ofs_in_node<871&&(inode->i_blocks/4+1)<871){
					if(is_inode_flag_set(inode,FI_INLINE_DELTA)){
						if(last_iaddr<871) left_iaddr=852*sizeof(__le32)-last_iaddr*sizeof(__le32)-1-delta_inline_size; // PAN: 872 -> ADDRS_PER_INODE(inode)
						else left_iaddr=0;
					}
					else
					{
						left_iaddr=852*sizeof(__le32)-dn.ofs_in_node*sizeof(__le32)-1;			
					}
					if(clen<256&&left_iaddr>(clen+sizeof(__le16)+1))
					{//255 because the delta index only maintains 1 byte to record the size of delta, which supports to record 255 bytes size, file size smaller than (922-50) * 4096 to have spare inline space for delta
						delta_compress_enable=1;//decide inline or not
					}
					else if(is_inode_flag_set(inode,FI_INLINE_DELTA) && clen<(256-81) && left_iaddr<= (clen+sizeof(__le16)+1))
					{
						if(delta_num>0){
							replace_flag=innode_data_replacement(file, &dn, page->index, cbuf,clen, delta_num, delta_inline_size, src_addr, dst_addr);
						}
					}
				}
			}
		}
#ifdef F2FS_MAIN_COMPRESS
		if(delta_compress_enable==0&&clen<819&&replace_flag==1&&inode->i_blocks>5) {
			f2fs_put_dnode(&dn);
			main_flag=f2fs_store_delta_in_main(inode,cbuf, clen, page->index, 0);	//5page to 1 in main delta
			set_new_dnode(&dn, inode, NULL, NULL, 0);
			err = f2fs_get_dnode_of_data(&dn, page->index, LOOKUP_NODE);
			if (err){
				goto delta_out;		
			}
			
		}
#endif
		/***********************************insert delta********************************/
		next_loc=872*sizeof(__le32)-6-delta_inline_size;
		if(delta_compress_enable==1){//insert delta 		
			ff1=dn.ofs_in_node, ff2=dn.ofs_in_node>>BITS_PER_BYTE;
			dst_addr[next_loc]=ff1;
			dst_addr[next_loc-1]=ff2;
			c=clen;
			dst_addr[next_loc-sizeof(__le16)]=c;//insert size 
			for(i=0;i<clen;i++) {
				dst_addr[next_loc-sizeof(__le16)-i-1]=cbuf[i];	//insert delta
				//printk(KERN_ALERT"compress xor len is:%d %d %d %d %d %d\n",clen, page->index,inode->i_ino, dn.ofs_in_node,dn.data_blkaddr, next_loc);
			}
			delta_inline_size=delta_inline_size+clen+sizeof(__le16)+1;
			delta_num++;
			c=delta_num;
			dst_addr[872*sizeof(__le32)-1]=c;  
			ff1=delta_inline_size, ff2=delta_inline_size>>BITS_PER_BYTE;
			dst_addr[872*sizeof(__le32)-2]=ff1;
			dst_addr[872*sizeof(__le32)-3]=ff2;
			if(!is_inode_flag_set(inode,FI_INLINE_DELTA)){
				ff1=dn.ofs_in_node, ff2=dn.ofs_in_node>>BITS_PER_BYTE;
				dst_addr[872*sizeof(__le32)-4]=ff1;
				dst_addr[872*sizeof(__le32)-5]=ff2;
			}			
			delta_flag=1;
			src_addr = inline_data_addr(inode, dn.inode_page);//cp updated dst addr to inline
			memcpy(src_addr, dst_addr, MAX_INLINE_DATA(inode));
		}
		if(delta_flag==1){
			set_page_dirty(dn.inode_page);
			if(!is_inode_flag_set(inode,FI_INLINE_DELTA)) {
				set_inode_flag(inode, FI_INLINE_DELTA);//mark delta compress flag
				set_inode_flag(inode, FI_APPEND_WRITE);//for recovery
				F2FS_I(inode)->i_flags = F2FS_I(inode)->i_flags | F2FS_DELTA_INLINE;
			}
			f2fs_clear_radix_tree_dirty_tag(page);
		}
		kfree(xor);
		kunmap(page);
		kfree(new_data);
		kfree(cbuf);
		kfree(fsdata);
		if(dst_addr!=NULL) kfree(dst_addr);
	}
	f2fs_put_dnode(&dn);
delta_out:	
#endif
/*************************************************************************/
	trace_android_fs_datawrite_end(inode, pos, len);
	trace_f2fs_write_end(inode, pos, len, copied);
	/*
	 * This should be come from len == PAGE_SIZE, and we expect copied
	 * should be PAGE_SIZE. Otherwise, we treat it with zero copied and
	 * let generic_perform_write() try to copy data again through copied=0.
	 */
	if (!PageUptodate(page)) {
		if (unlikely(copied != len))
			copied = 0;
		else
			SetPageUptodate(page);
	}

#ifdef CONFIG_F2FS_FS_COMPRESSION
	/* overwrite compressed file */
	if (f2fs_compressed_file(inode) && fsdata) {
		f2fs_compress_write_end(inode, fsdata, page->index, copied);
		f2fs_update_time(F2FS_I_SB(inode), REQ_TIME);
		return copied;
	}
#endif

	if (!copied)
		goto unlock_out;
#ifdef F2FS_DELTA_COMPRESS
	if(delta_flag==0 || replace_flag==1) {
#ifdef F2FS_MAIN_COMPRESS
		if(main_flag==0)
#endif		
			set_page_dirty(page);

	}
#else
	set_page_dirty(page);
#endif
	if (pos + copied > i_size_read(inode) &&
	    !f2fs_verity_in_progress(inode))
		f2fs_i_size_write(inode, pos + copied);
unlock_out:
	f2fs_put_page(page, 1);
	f2fs_update_time(F2FS_I_SB(inode), REQ_TIME);
	return copied;
}

static int check_direct_IO(struct inode *inode, struct iov_iter *iter,
			   loff_t offset)
{
	unsigned i_blkbits = READ_ONCE(inode->i_blkbits);
	unsigned blkbits = i_blkbits;
	unsigned blocksize_mask = (1 << blkbits) - 1;
	unsigned long align = offset | iov_iter_alignment(iter);
	struct block_device *bdev = inode->i_sb->s_bdev;

	if (align & blocksize_mask) {
		if (bdev)
			blkbits = blksize_bits(bdev_logical_block_size(bdev));
		blocksize_mask = (1 << blkbits) - 1;
		if (align & blocksize_mask)
			return -EINVAL;
		return 1;
	}
	return 0;
}

static void f2fs_dio_end_io(struct bio *bio)
{
	struct f2fs_private_dio *dio = bio->bi_private;

	dec_page_count(F2FS_I_SB(dio->inode),
			dio->write ? F2FS_DIO_WRITE : F2FS_DIO_READ);

	bio->bi_private = dio->orig_private;
	bio->bi_end_io = dio->orig_end_io;

	kvfree(dio);

	bio_endio(bio);
}

static void f2fs_dio_submit_bio(struct bio *bio, struct inode *inode,
							loff_t file_offset)
{
	struct f2fs_private_dio *dio;
	bool write = (bio_op(bio) == REQ_OP_WRITE);

	dio = f2fs_kzalloc(F2FS_I_SB(inode),
			sizeof(struct f2fs_private_dio), GFP_NOFS);
	if (!dio)
		goto out;

	dio->inode = inode;
	dio->orig_end_io = bio->bi_end_io;
	dio->orig_private = bio->bi_private;
	dio->write = write;

	bio->bi_end_io = f2fs_dio_end_io;
	bio->bi_private = dio;

	inc_page_count(F2FS_I_SB(inode),
			write ? F2FS_DIO_WRITE : F2FS_DIO_READ);

	submit_bio(bio);
	return;
out:
	bio->bi_status = BLK_STS_IOERR;
	bio_endio(bio);
}

static ssize_t f2fs_direct_IO(struct kiocb *iocb, struct iov_iter *iter)
{
	struct address_space *mapping = iocb->ki_filp->f_mapping;
	struct inode *inode = mapping->host;
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
	struct f2fs_inode_info *fi = F2FS_I(inode);
	size_t count = iov_iter_count(iter);
	loff_t offset = iocb->ki_pos;
	int rw = iov_iter_rw(iter);
	int err;
	enum rw_hint hint = iocb->ki_hint;
	int whint_mode = F2FS_OPTION(sbi).whint_mode;
	bool do_opu;

	err = check_direct_IO(inode, iter, offset);
	if (err)
		return err < 0 ? err : 0;

	if (f2fs_force_buffered_io(inode, iocb, iter))
		return 0;

	do_opu = allow_outplace_dio(inode, iocb, iter);

	trace_f2fs_direct_IO_enter(inode, offset, count, rw);

	if (trace_android_fs_dataread_start_enabled() &&
	    (rw == READ)) {
		char *path, pathbuf[MAX_TRACE_PATHBUF_LEN];

		path = android_fstrace_get_pathname(pathbuf,
						    MAX_TRACE_PATHBUF_LEN,
						    inode);
		trace_android_fs_dataread_start(inode, offset,
						count, current->pid, path,
						current->comm);
	}
	if (trace_android_fs_datawrite_start_enabled() &&
	    (rw == WRITE)) {
		char *path, pathbuf[MAX_TRACE_PATHBUF_LEN];

		path = android_fstrace_get_pathname(pathbuf,
						    MAX_TRACE_PATHBUF_LEN,
						    inode);
		trace_android_fs_datawrite_start(inode, offset, count,
						 current->pid, path,
						 current->comm);
	}

	if (rw == WRITE && whint_mode == WHINT_MODE_OFF)
		iocb->ki_hint = WRITE_LIFE_NOT_SET;

	if (iocb->ki_flags & IOCB_NOWAIT) {
		if (!down_read_trylock(&fi->i_gc_rwsem[rw])) {
			iocb->ki_hint = hint;
			err = -EAGAIN;
			goto out;
		}
		if (do_opu && !down_read_trylock(&fi->i_gc_rwsem[READ])) {
			up_read(&fi->i_gc_rwsem[rw]);
			iocb->ki_hint = hint;
			err = -EAGAIN;
			goto out;
		}
	} else {
		down_read(&fi->i_gc_rwsem[rw]);
		if (do_opu)
			down_read(&fi->i_gc_rwsem[READ]);
	}

	err = __blockdev_direct_IO(iocb, inode, inode->i_sb->s_bdev,
			iter, rw == WRITE ? get_data_block_dio_write :
			get_data_block_dio, NULL, f2fs_dio_submit_bio,
			DIO_LOCKING | DIO_SKIP_HOLES);

	if (do_opu)
		up_read(&fi->i_gc_rwsem[READ]);

	up_read(&fi->i_gc_rwsem[rw]);

	if (rw == WRITE) {
		if (whint_mode == WHINT_MODE_OFF)
			iocb->ki_hint = hint;
		if (err > 0) {
			f2fs_update_iostat(F2FS_I_SB(inode), APP_DIRECT_IO,
									err);
			if (!do_opu)
				set_inode_flag(inode, FI_UPDATE_WRITE);
		} else if (err < 0) {
			f2fs_write_failed(mapping, offset + count);
		}
	}

out:
	if (trace_android_fs_dataread_start_enabled() &&
	    (rw == READ))
		trace_android_fs_dataread_end(inode, offset, count);
	if (trace_android_fs_datawrite_start_enabled() &&
	    (rw == WRITE))
		trace_android_fs_datawrite_end(inode, offset, count);

	trace_f2fs_direct_IO_exit(inode, offset, count, rw, err);

	return err;
}

void f2fs_invalidate_page(struct page *page, unsigned int offset,
							unsigned int length)
{
	struct inode *inode = page->mapping->host;
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);

	if (inode->i_ino >= F2FS_ROOT_INO(sbi) &&
		(offset % PAGE_SIZE || length != PAGE_SIZE))
		return;

	if (PageDirty(page)) {
		if (inode->i_ino == F2FS_META_INO(sbi)) {
			dec_page_count(sbi, F2FS_DIRTY_META);
		} else if (inode->i_ino == F2FS_NODE_INO(sbi)) {
			dec_page_count(sbi, F2FS_DIRTY_NODES);
		} else {
			inode_dec_dirty_pages(inode);
			f2fs_remove_dirty_inode(inode);
		}
	}

	clear_cold_data(page);

	if (IS_ATOMIC_WRITTEN_PAGE(page))
		return f2fs_drop_inmem_page(inode, page);

	f2fs_clear_page_private(page);
}

int f2fs_release_page(struct page *page, gfp_t wait)
{
	/* If this is dirty page, keep PagePrivate */
	if (PageDirty(page))
		return 0;

	/* This is atomic written page, keep Private */
	if (IS_ATOMIC_WRITTEN_PAGE(page))
		return 0;

	clear_cold_data(page);
	f2fs_clear_page_private(page);
	return 1;
}

static int f2fs_set_data_page_dirty(struct page *page)
{
	struct inode *inode = page_file_mapping(page)->host;

	trace_f2fs_set_page_dirty(page, DATA);

	if (!PageUptodate(page))
		SetPageUptodate(page);
	if (PageSwapCache(page))
		return __set_page_dirty_nobuffers(page);

	if (f2fs_is_atomic_file(inode) && !f2fs_is_commit_atomic_write(inode)) {
		if (!IS_ATOMIC_WRITTEN_PAGE(page)) {
			f2fs_register_inmem_page(inode, page);
			return 1;
		}
		/*
		 * Previously, this page has been registered, we just
		 * return here.
		 */
		return 0;
	}

	if (!PageDirty(page)) {
		__set_page_dirty_nobuffers(page);
		f2fs_update_dirty_page(inode, page);
		return 1;
	}
	return 0;
}

static sector_t f2fs_bmap(struct address_space *mapping, sector_t block)
{
	struct inode *inode = mapping->host;

	if (f2fs_has_inline_data(inode))
		return 0;

	/* make sure allocating whole blocks */
	if (mapping_tagged(mapping, PAGECACHE_TAG_DIRTY))
		filemap_write_and_wait(mapping);

	return generic_block_bmap(mapping, block, get_data_block_bmap);
}

#ifdef CONFIG_MIGRATION
#include <linux/migrate.h>

int f2fs_migrate_page(struct address_space *mapping,
		struct page *newpage, struct page *page, enum migrate_mode mode)
{
	int rc, extra_count;
	struct f2fs_inode_info *fi = F2FS_I(mapping->host);
	bool atomic_written = IS_ATOMIC_WRITTEN_PAGE(page);

	BUG_ON(PageWriteback(page));

	/* migrating an atomic written page is safe with the inmem_lock hold */
	if (atomic_written) {
		if (mode != MIGRATE_SYNC)
			return -EBUSY;
		if (!mutex_trylock(&fi->inmem_lock))
			return -EAGAIN;
	}

	/* one extra reference was held for atomic_write page */
	extra_count = atomic_written ? 1 : 0;
	rc = migrate_page_move_mapping(mapping, newpage,
				page, NULL, mode, extra_count);
	if (rc != MIGRATEPAGE_SUCCESS) {
		if (atomic_written)
			mutex_unlock(&fi->inmem_lock);
		return rc;
	}

	if (atomic_written) {
		struct inmem_pages *cur;
		list_for_each_entry(cur, &fi->inmem_pages, list)
			if (cur->page == page) {
				cur->page = newpage;
				break;
			}
		mutex_unlock(&fi->inmem_lock);
		put_page(page);
		get_page(newpage);
	}

	if (PagePrivate(page)) {
		f2fs_set_page_private(newpage, page_private(page));
		f2fs_clear_page_private(page);
	}

	if (mode != MIGRATE_SYNC_NO_COPY)
		migrate_page_copy(newpage, page);
	else
		migrate_page_states(newpage, page);

	return MIGRATEPAGE_SUCCESS;
}
#endif

#ifdef CONFIG_SWAP
/* Copied from generic_swapfile_activate() to check any holes */
static int check_swap_activate(struct swap_info_struct *sis,
				struct file *swap_file, sector_t *span)
{
	struct address_space *mapping = swap_file->f_mapping;
	struct inode *inode = mapping->host;
	unsigned blocks_per_page;
	unsigned long page_no;
	unsigned blkbits;
	sector_t probe_block;
	sector_t last_block;
	sector_t lowest_block = -1;
	sector_t highest_block = 0;
	int nr_extents = 0;
	int ret;

	blkbits = inode->i_blkbits;
	blocks_per_page = PAGE_SIZE >> blkbits;

	/*
	 * Map all the blocks into the extent list.  This code doesn't try
	 * to be very smart.
	 */
	probe_block = 0;
	page_no = 0;
	last_block = i_size_read(inode) >> blkbits;
	while ((probe_block + blocks_per_page) <= last_block &&
			page_no < sis->max) {
		unsigned block_in_page;
		sector_t first_block;

		cond_resched();

		first_block = bmap(inode, probe_block);
		if (first_block == 0)
			goto bad_bmap;

		/*
		 * It must be PAGE_SIZE aligned on-disk
		 */
		if (first_block & (blocks_per_page - 1)) {
			probe_block++;
			goto reprobe;
		}

		for (block_in_page = 1; block_in_page < blocks_per_page;
					block_in_page++) {
			sector_t block;

			block = bmap(inode, probe_block + block_in_page);
			if (block == 0)
				goto bad_bmap;
			if (block != first_block + block_in_page) {
				/* Discontiguity */
				probe_block++;
				goto reprobe;
			}
		}

		first_block >>= (PAGE_SHIFT - blkbits);
		if (page_no) {	/* exclude the header page */
			if (first_block < lowest_block)
				lowest_block = first_block;
			if (first_block > highest_block)
				highest_block = first_block;
		}

		/*
		 * We found a PAGE_SIZE-length, PAGE_SIZE-aligned run of blocks
		 */
		ret = add_swap_extent(sis, page_no, 1, first_block);
		if (ret < 0)
			goto out;
		nr_extents += ret;
		page_no++;
		probe_block += blocks_per_page;
reprobe:
		continue;
	}
	ret = nr_extents;
	*span = 1 + highest_block - lowest_block;
	if (page_no == 0)
		page_no = 1;	/* force Empty message */
	sis->max = page_no;
	sis->pages = page_no - 1;
	sis->highest_bit = page_no - 1;
out:
	return ret;
bad_bmap:
	pr_err("swapon: swapfile has holes\n");
	return -EINVAL;
}

static int f2fs_swap_activate(struct swap_info_struct *sis, struct file *file,
				sector_t *span)
{
	struct inode *inode = file_inode(file);
	int ret;

	if (!S_ISREG(inode->i_mode))
		return -EINVAL;

	if (f2fs_readonly(F2FS_I_SB(inode)->sb))
		return -EROFS;

	ret = f2fs_convert_inline_inode(inode);
	if (ret)
		return ret;

	if (f2fs_disable_compressed_file(inode))
		return -EINVAL;

	ret = check_swap_activate(sis, file, span);
	if (ret < 0)
		return ret;

	set_inode_flag(inode, FI_PIN_FILE);
	f2fs_precache_extents(inode);
	f2fs_update_time(F2FS_I_SB(inode), REQ_TIME);
	return ret;
}

static void f2fs_swap_deactivate(struct file *file)
{
	struct inode *inode = file_inode(file);

	clear_inode_flag(inode, FI_PIN_FILE);
}
#else
static int f2fs_swap_activate(struct swap_info_struct *sis, struct file *file,
				sector_t *span)
{
	return -EOPNOTSUPP;
}

static void f2fs_swap_deactivate(struct file *file)
{
}
#endif

const struct address_space_operations f2fs_dblock_aops = {
	.readpage	= f2fs_read_data_page,
	.readpages	= f2fs_read_data_pages,
	.writepage	= f2fs_write_data_page,
	.writepages	= f2fs_write_data_pages,
	.write_begin	= f2fs_write_begin,
	.write_end	= f2fs_write_end,
	.set_page_dirty	= f2fs_set_data_page_dirty,
	.invalidatepage	= f2fs_invalidate_page,
	.releasepage	= f2fs_release_page,
	.direct_IO	= f2fs_direct_IO,
	.bmap		= f2fs_bmap,
	.swap_activate  = f2fs_swap_activate,
	.swap_deactivate = f2fs_swap_deactivate,
#ifdef CONFIG_MIGRATION
	.migratepage    = f2fs_migrate_page,
#endif
};

void f2fs_clear_radix_tree_dirty_tag(struct page *page)
{
	struct address_space *mapping = page_mapping(page);
	unsigned long flags;

	xa_lock_irqsave(&mapping->i_pages, flags);
	radix_tree_tag_clear(&mapping->i_pages, page_index(page),
						PAGECACHE_TAG_DIRTY);
	xa_unlock_irqrestore(&mapping->i_pages, flags);
}

int __init f2fs_init_post_read_processing(void)
{
	bio_post_read_ctx_cache =
		kmem_cache_create("f2fs_bio_post_read_ctx",
				  sizeof(struct bio_post_read_ctx), 0, 0, NULL);
	if (!bio_post_read_ctx_cache)
		goto fail;
	bio_post_read_ctx_pool =
		mempool_create_slab_pool(NUM_PREALLOC_POST_READ_CTXS,
					 bio_post_read_ctx_cache);
	if (!bio_post_read_ctx_pool)
		goto fail_free_cache;
	return 0;

fail_free_cache:
	kmem_cache_destroy(bio_post_read_ctx_cache);
fail:
	return -ENOMEM;
}

void f2fs_destroy_post_read_processing(void)
{
	mempool_destroy(bio_post_read_ctx_pool);
	kmem_cache_destroy(bio_post_read_ctx_cache);
}

int f2fs_init_post_read_wq(struct f2fs_sb_info *sbi)
{
	if (!f2fs_sb_has_encrypt(sbi) &&
		!f2fs_sb_has_verity(sbi) &&
		!f2fs_sb_has_compression(sbi))
		return 0;

	sbi->post_read_wq = alloc_workqueue("f2fs_post_read_wq",
						 WQ_UNBOUND | WQ_HIGHPRI,
						 num_online_cpus());
	if (!sbi->post_read_wq)
		return -ENOMEM;
	return 0;
}

void f2fs_destroy_post_read_wq(struct f2fs_sb_info *sbi)
{
	if (sbi->post_read_wq)
		destroy_workqueue(sbi->post_read_wq);
}

int __init f2fs_init_bio_entry_cache(void)
{
	bio_entry_slab = f2fs_kmem_cache_create("bio_entry_slab",
			sizeof(struct bio_entry));
	if (!bio_entry_slab)
		return -ENOMEM;
	return 0;
}

void f2fs_destroy_bio_entry_cache(void)
{
	kmem_cache_destroy(bio_entry_slab);
}
#ifdef F2FS_DELTA_COMPRESS
/************************************************************/
int f2fs_decompress_delta(struct page *page){
	struct address_space *mapping = page_file_mapping(page);
	struct inode *inode;
	struct dnode_of_data dn;
	size_t rlen,clen;
	struct timeval tstart, tend;
	struct f2fs_node *rn;
	int i,j,next_index,ret,err,decomp_time,base = 0,flag=0,delta_num=0;
	char *src_addr,*dst_addr,*page_data,*cbuf=NULL,* new_data=NULL,* tp=NULL;
	unsigned char ff1, ff2, c,ch, ch1;
	__le32 *addr_array;
	block_t base_blkaddr;
	if (!mapping || !mapping->host || !F2FS_I_SB(mapping->host) || !NM_I(F2FS_I_SB(mapping->host)) || !F2FS_I_SB(mapping->host)->mounted) return false;
	if(!PageLocked(page)) {
		if(trylock_page(page)) flag=1;
	}
	inode = mapping->host;

	if(is_inode_flag_set(inode,FI_INLINE_DELTA)){
		set_new_dnode(&dn, inode, NULL, NULL, 0);
		err = f2fs_get_dnode_of_data(&dn, page->index, LOOKUP_NODE);
		if (err){
			f2fs_put_dnode(&dn);
			return err;
		}
		do_gettimeofday(&tstart);
		src_addr = inline_data_addr(inode, dn.inode_page);
		dst_addr = kmalloc(PAGE_SIZE, GFP_NOFS);
		memcpy(dst_addr, src_addr, MAX_INLINE_DATA(inode));
		next_index=872*sizeof(__le32)-1;  
		c=dst_addr[next_index];  
		delta_num=c;
		//fetch delta
		next_index=872*sizeof(__le32)-6; 
		for(i=0;i<delta_num;i++){
			ff1=dst_addr[next_index],ff2=dst_addr[next_index-1]; 
			block_t blkaddr=ff2;
			blkaddr = (blkaddr << BITS_PER_BYTE) | ff1;
			c=dst_addr[next_index-sizeof(__le16)];
			rlen=c;

			if (IS_INODE(dn.inode_page) && f2fs_has_extra_attr(inode))
				base = get_extra_isize(inode);
			rn = F2FS_NODE(dn.inode_page);
			addr_array = blkaddr_in_node(rn);
			base_blkaddr = le32_to_cpu(addr_array[base+blkaddr]);
			if (__is_valid_data_blkaddr(base_blkaddr) && !f2fs_is_valid_blkaddr(F2FS_I_SB(inode), base_blkaddr, DATA_GENERIC_ENHANCE)) {
				printk(KERN_ALERT"invalid blkaddr in decomp:%d %lu %lu\n",rlen, blkaddr, base_blkaddr);
				f2fs_put_dnode(&dn);
				return -1;	
			}

			if(blkaddr==dn.ofs_in_node){
				tp=kmalloc(rlen,GFP_NOFS);
				for(j=0;j<rlen;j++){
					tp[j]=dst_addr[next_index-sizeof(__le16)-1-j];
					//printk(KERN_ALERT"find delta in read decomp:%d %d %hd\n",rlen,next_index,dst_addr[next_index-sizeof(__le16)-1-j]);
				}
				break;
			}
			next_index=next_index-sizeof(__le16)-1-rlen;
		}
		if(tp!=NULL&&rlen!=0){
			clen=PAGE_SIZE;
			
			cbuf=f2fs_kzalloc(F2FS_I_SB(inode),clen,GFP_NOFS);	
			ret = lzo1x_decompress_safe(tp, rlen,
						cbuf, &clen);
			if (ret != LZO_E_OK) {
				printk_ratelimited("%sF2FS-fs (%s): lzo decompress failed, ret:%d\n",
						KERN_ERR, F2FS_I_SB(inode)->sb->s_id, ret);
				f2fs_put_dnode(&dn);
				return false;
			}
			do_gettimeofday(&tend);
			decomp_time=1000000*(tend.tv_sec-tstart.tv_sec)+(tend.tv_usec-tstart.tv_usec);
			//printk(KERN_ALERT"decompress time is:%lu\n",decomp_time);
		//merge delta to base		
			page_data=kmap(page);
			new_data=kmalloc(PAGE_SIZE,GFP_NOFS);
			
			for(i=0;i<PAGE_SIZE;i++){
				ch=cbuf[i];
				ch1=page_data[i];
				new_data[i]=ch^ch1;
			}
			memcpy(page_data,new_data,PAGE_SIZE);//restore new data

			kunmap(page);
			kfree(tp);
			kfree(new_data);
			kfree(cbuf);
			if (!PageUptodate(page)) SetPageUptodate(page);
		}
		kfree(dst_addr);
		f2fs_put_dnode(&dn);
	}
	if(flag) {
		unlock_page(page);
//		put_page(page);
	}
	return 0;
}

int f2fs_retrieve_delta(struct inode *inode, unsigned int ofs_in_node)
{
	int i, j, next_loc, start_loc, end_loc, cur_ofs,offset,err=0,tosize=0,conflict_num=0, conflict_size=0,delta_num=0,delta_inline_size=0, base=0,clen=0;
	char *src_addr=NULL,*dst_addr=NULL, *tp=NULL, *cbuf=NULL;
	unsigned char c,ff1,ff2;
	size_t dsize;
	int base_ofs_innode[75];
	size_t delta_size_innode[75];
	block_t base_blk_addr[75];
	struct dnode_of_data dn;
	struct page *basepage;
	struct address_space *mapping = inode->i_mapping;
	struct page *ipage;
	struct f2fs_node *rn;
	__le32 *addr_array;

	if (!mapping || !mapping->host || !F2FS_I_SB(mapping->host) || !NM_I(F2FS_I_SB(mapping->host)) || !F2FS_I_SB(mapping->host)->mounted) return false;
	if(!is_inode_flag_set(inode,FI_INLINE_DELTA)) return 0;

	/*first record all compressed index in inline*/
	ipage = f2fs_get_node_page(F2FS_I_SB(inode), inode->i_ino);
	if (IS_ERR(ipage)) {
		err = PTR_ERR(ipage);
		printk(KERN_ALERT"cannot find ipage page in retrieve\n");
		return err;
	}
	if(!is_inode_flag_set(inode,FI_INLINE_DELTA)) {
		f2fs_put_page(ipage,1);
		return 0;
	}
	f2fs_wait_on_page_writeback(ipage, NODE, true, true);
	memset(base_ofs_innode,0,sizeof(int)*75);
	memset(delta_size_innode,0,sizeof(size_t)*75);
	memset(base_blk_addr,0,sizeof(block_t)*75);
	dst_addr=kmalloc(PAGE_SIZE, GFP_NOFS);//cp inline to dst addr
	src_addr = inline_data_addr(inode, ipage);
	memcpy(dst_addr, src_addr, MAX_INLINE_DATA(inode));	
	//find conflict delta
	next_loc=872*sizeof(__le32)-1;  
	c=dst_addr[next_loc];  
	delta_num=c;
	ff1=dst_addr[next_loc-1], ff2=dst_addr[next_loc-2];
	delta_inline_size=ff2;
	delta_inline_size = (delta_inline_size << BITS_PER_BYTE) | ff1;
	if (IS_INODE(ipage) && f2fs_has_extra_attr(inode))
		base = get_extra_isize(inode);
	rn = F2FS_NODE(ipage);
	addr_array = blkaddr_in_node(rn);	
	if(((ofs_in_node+1)*sizeof(__le32)-1)<(872*sizeof(__le32)-6-delta_inline_size)) {
		kfree(dst_addr);
		f2fs_put_page(ipage, 1);
		return 0;
	}
	next_loc=872*sizeof(__le32)-6;
	for(i=0;i<delta_num;i++)
	{
		ff1=dst_addr[next_loc],ff2=dst_addr[next_loc-1];
		offset = ff2;
		offset = (ff2 << BITS_PER_BYTE) | ff1; 
		c=dst_addr[next_loc-sizeof(__le16)];
		dsize=c;
		if(((ofs_in_node+1)*sizeof(__le32)-1)>=(next_loc-sizeof(__le16)-1-dsize)){
			base_ofs_innode[conflict_num]=offset;
			delta_size_innode[conflict_num]=dsize;
			base_blk_addr[conflict_num] = le32_to_cpu(addr_array[base+offset]);
			if(conflict_num==0) {
				start_loc=next_loc;
			}
			conflict_num++;
			conflict_size+=(dsize+sizeof(__le16)+1);			
		}
		next_loc=next_loc-dsize-sizeof(__le16)-1;
	}
	end_loc=872*sizeof(__le32)-6-delta_inline_size;
	delta_num-=conflict_num;
	delta_inline_size-=conflict_size;	
	f2fs_truncate_inline_delta(inode, ipage, start_loc, end_loc, delta_num,delta_inline_size);
	if(delta_num==0 || delta_inline_size==0) {
		clear_inode_flag(inode, FI_INLINE_DELTA);//mark delta compress flag	
		F2FS_I(inode)->i_flags &= ~F2FS_DELTA_INLINE;
	}	
	set_inode_flag(inode, FI_DELTA_TRUNCATING);
	F2FS_I(inode)->i_flags &= F2FS_DELTA_TRUNCATING;
	set_inode_flag(inode, FI_FINISH_TRUNCATE);/*to avoid new compress during truncate which could contaminate the inline area has been truncated*/
	F2FS_I(inode)->i_flags &= F2FS_DELTA_FINISH;
	f2fs_put_page(ipage,1);
#ifdef F2FS_MAIN_COMPRESS
	for(i=0;i<conflict_num;i++){
		cur_ofs= delta_size_innode[i];
		tosize=0;
		for(j=0;j<i;j++) tosize += delta_size_innode[j];
		tosize+=((sizeof(__le16)+1)*i);
		clen= delta_size_innode[i];
		tp=kmalloc(clen, GFP_NOFS);
		for(j=0;j<clen;j++) tp[j]=dst_addr[start_loc-tosize-j];
		printk(KERN_ALERT"test in f2fs retrieve delta:%d\n",inode->i_ino);
		f2fs_store_delta_in_main(inode ,tp, clen,base_ofs_innode[i],1);	
	}

#else
wait_unlock:
		/*read new pages*/
	for(i=0;i<conflict_num;i++)
	{
		basepage = f2fs_pagecache_get_page(mapping, base_ofs_innode[i],
				FGP_LOCK | FGP_WRITE | FGP_CREAT, GFP_NOFS);
		if (!basepage) {
			err = -ENOMEM;
			printk(KERN_ALERT"get basepage failed in cache\n");
			return err;
		}
		f2fs_lock_op(F2FS_I_SB(inode));
		set_new_dnode(&dn, inode, NULL, NULL, 0);
		err = f2fs_get_dnode_of_data(&dn, basepage->index, LOOKUP_NODE);
		if (err){
			f2fs_unlock_op(F2FS_I_SB(inode));
			f2fs_put_page(basepage, 1);	
			printk(KERN_ALERT"get dnode failed in f2fs_retrieve_inode_delta\n");
			return err;
		}
		cur_ofs= delta_size_innode[i];
		tosize=0;
		for(j=0;j<i;j++) tosize += delta_size_innode[j];
		tosize+=((sizeof(__le16)+1)*i);
	/*need to read from flash and decompress*/
		if (!PageUptodate(basepage)) {
			/*read base blkaddr*/
			if (__is_valid_data_blkaddr(base_blk_addr[i]) && !f2fs_is_valid_blkaddr(F2FS_I_SB(inode), base_blk_addr[i], DATA_GENERIC_ENHANCE)) {
				printk(KERN_ALERT"invalid blkaddr in inode retrieve:%lu %d\n", base_blk_addr[i],inode->i_ino);
				f2fs_put_dnode(&dn);
				f2fs_unlock_op(F2FS_I_SB(inode));
				f2fs_put_page(basepage, 1);	
				return -1;	
			}
			err = f2fs_submit_page_read(inode, basepage, base_blk_addr[i]);
			if (err || unlikely(basepage->mapping != inode->i_mapping)) {
				printk(KERN_ALERT"cannot find base page in flash in inode retrieve:%d %d %d\n",inode->i_ino, basepage->index, base_blk_addr[i]);
				f2fs_put_dnode(&dn);
				f2fs_unlock_op(F2FS_I_SB(inode));
				f2fs_put_page(basepage, 1);	
				return err;
			}
			tp=kmalloc(cur_ofs, GFP_NOFS);
			next_loc=start_loc-tosize;
			for(j=0;j<cur_ofs;j++) tp[j]=dst_addr[next_loc-sizeof(__le16)-1-j];
			err=f2fs_decompress_delta_for_retrieve(basepage, tp, cur_ofs);
			if (err){
				printk(KERN_ALERT"decompress failed in inode retrieve\n");
				f2fs_put_dnode(&dn);
				f2fs_unlock_op(F2FS_I_SB(inode));
				if(PageLocked(basepage)) f2fs_put_page(basepage, 1);	
				else put_page(basepage);
				congestion_wait(BLK_RW_ASYNC, HZ/50);	
				goto wait_unlock;
			}
			SetPageUptodate(basepage);
			kfree(tp);
			//printk(KERN_ALERT"get base in flash in retrieve:%d\n",inode->i_ino);
		}
		err=f2fs_convert_inline_delta(&dn, basepage);/*perform page writeback*/
		if(err) {
			printk(KERN_ALERT"err in convert inline delta1:%d %d %d\n", inode->i_ino, current->pid, current->tgid);
			f2fs_put_dnode(&dn);
			f2fs_unlock_op(F2FS_I_SB(inode));
			if(PageLocked(basepage)) f2fs_put_page(basepage, 1);	
			else put_page(basepage);	
			congestion_wait(BLK_RW_ASYNC, HZ/50);
			goto wait_unlock;
		}	
		f2fs_put_dnode(&dn);
		f2fs_unlock_op(F2FS_I_SB(inode));
		if(PageLocked(basepage)) f2fs_put_page(basepage, 1);
	}
#endif	
	f2fs_remove_dirty_inode(inode);
	/* this converted inline_data should be recovered. */
	set_inode_flag(inode, FI_APPEND_WRITE);
	clear_inode_flag(inode, FI_DELTA_TRUNCATING);
	F2FS_I(inode)->i_flags &= ~F2FS_DELTA_TRUNCATING;
	f2fs_balance_fs(F2FS_I_SB(inode), dn.node_changed);
	kfree(dst_addr);
	return 0;

}



int f2fs_retrieve_inode_delta(struct inode *inode)
{
	int i, j, next_loc, end_loc, cur_ofs, offset, err=0, tosize=0, delta_num=0, delta_inline_size=0,last_iaddr=0;
	char *src_addr=NULL,*dst_addr=NULL, *tp=NULL;
	unsigned char c,ff1,ff2;
	size_t dsize;
	int base_ofs_innode[75];
	size_t delta_size_innode[75];
	block_t base_blk_addr[75];
	struct dnode_of_data dn;
	struct page *basepage;
	struct address_space *mapping = inode->i_mapping;
	struct page *ipage;
	struct f2fs_node *rn;
	__le32 *addr_array;
	int base = 0;


	if (!mapping || !mapping->host || !F2FS_I_SB(mapping->host) || !NM_I(F2FS_I_SB(mapping->host)) || !F2FS_I_SB(mapping->host)->mounted) 
	{
		printk(KERN_ALERT"null mapping in retrieve inode\n");
		return false;
	}
	if(!is_inode_flag_set(inode,FI_INLINE_DELTA)) {
		return 0;
	}

	/*first record all compressed index in inline*/
	ipage = f2fs_get_node_page(F2FS_I_SB(inode), inode->i_ino);
	if (IS_ERR(ipage)) {
		err = PTR_ERR(ipage);
		printk(KERN_ALERT"cannot find ipage page in retrieve\n");
		return err;
	}
	if(!is_inode_flag_set(inode,FI_INLINE_DELTA)) { /*to avoid concurrent threads traverse in this code*/
		f2fs_put_page(ipage,1);
		return 0;
	}
	f2fs_wait_on_page_writeback(ipage, NODE, true, true);
	memset(base_ofs_innode,0,sizeof(int)*75);
	memset(delta_size_innode,0,sizeof(size_t)*75);
	memset(base_blk_addr,0,sizeof(block_t)*75);
	dst_addr=kmalloc(PAGE_SIZE, GFP_NOFS);//cp inline to dst addr
	src_addr = inline_data_addr(inode, ipage);
	memcpy(dst_addr, src_addr, MAX_INLINE_DATA(inode));	
	//find conflict delta
	next_loc=872*sizeof(__le32)-1;  
	c=dst_addr[next_loc];  
	delta_num=c;
	ff1=dst_addr[next_loc-1], ff2=dst_addr[next_loc-2];
	delta_inline_size=ff2;
	delta_inline_size = (delta_inline_size << BITS_PER_BYTE) | ff1;
	if (IS_INODE(ipage) && f2fs_has_extra_attr(inode))
		base = get_extra_isize(inode);
	rn = F2FS_NODE(ipage);
	addr_array = blkaddr_in_node(rn);	
	next_loc=872*sizeof(__le32)-6;
	for(i=0;i<delta_num;i++)
	{
		ff1=dst_addr[next_loc],ff2=dst_addr[next_loc-1];
		offset = ff2;
		offset = (ff2 << BITS_PER_BYTE) | ff1; 
		c=dst_addr[next_loc-sizeof(__le16)];
		dsize=c;
		base_ofs_innode[i]=offset;
		delta_size_innode[i]=dsize;
		base_blk_addr[i] = le32_to_cpu(addr_array[base+offset]);		
		next_loc=next_loc-dsize-sizeof(__le16)-1;
	}
	next_loc=872*sizeof(__le32)-6;
	end_loc=872*sizeof(__le32)-6-delta_inline_size;
	f2fs_truncate_inline_delta(inode, ipage, next_loc, end_loc, 0, 0);
	clear_inode_flag(inode, FI_INLINE_DELTA);//mark delta compress flag	
	F2FS_I(inode)->i_flags &= ~F2FS_DELTA_INLINE;
	set_inode_flag(inode, FI_DELTA_TRUNCATING);
	F2FS_I(inode)->i_flags &= F2FS_DELTA_TRUNCATING;
	set_inode_flag(inode, FI_FINISH_TRUNCATE);
	F2FS_I(inode)->i_flags &= F2FS_DELTA_FINISH;
	f2fs_put_page(ipage,1);
wait_unlock:
		/*read new pages*/
	for(i=0;i<delta_num;i++)
	{
		basepage = f2fs_pagecache_get_page(mapping, base_ofs_innode[i],
				FGP_LOCK | FGP_WRITE | FGP_CREAT, GFP_NOFS);
		if (!basepage) {
			err = -ENOMEM;
			printk(KERN_ALERT"get basepage failed in cache\n");
			return err;
		}
		f2fs_lock_op(F2FS_I_SB(inode));
		set_new_dnode(&dn, inode, NULL, NULL, 0);
		err = f2fs_get_dnode_of_data(&dn, basepage->index, LOOKUP_NODE);
		if (err){
			f2fs_unlock_op(F2FS_I_SB(inode));
			f2fs_put_page(basepage, 1);
			printk(KERN_ALERT"get dnode failed in f2fs_retrieve_inode_delta\n");
			return err;
		}
		cur_ofs= delta_size_innode[i];
		tosize=0;
		for(j=0;j<i;j++) tosize += delta_size_innode[j];
		tosize+=((sizeof(__le16)+1)*i);
	/*need to read from flash and decompress*/
		if (!PageUptodate(basepage)) {
			/*read base blkaddr*/
			if (__is_valid_data_blkaddr(base_blk_addr[i]) && !f2fs_is_valid_blkaddr(F2FS_I_SB(inode), base_blk_addr[i], DATA_GENERIC_ENHANCE)) {
				printk(KERN_ALERT"invalid blkaddr in inode retrieve:%lu %d\n", base_blk_addr[i],inode->i_ino);
				f2fs_put_dnode(&dn);
				f2fs_unlock_op(F2FS_I_SB(inode));
				f2fs_put_page(basepage, 1);	
				return -1;	
			}
			err = f2fs_submit_page_read(inode, basepage, base_blk_addr[i]);
			if (err || unlikely(basepage->mapping != inode->i_mapping)) {
				printk(KERN_ALERT"cannot find base page in flash in inode retrieve:%d %d %d\n",inode->i_ino, basepage->index, base_blk_addr[i]);
				f2fs_put_dnode(&dn);
				f2fs_unlock_op(F2FS_I_SB(inode));
				f2fs_put_page(basepage, 1);	
				return err;
			}
			tp=kmalloc(cur_ofs, GFP_NOFS);
			next_loc=872*sizeof(__le32)-6-tosize;
			for(j=0;j<cur_ofs;j++) tp[j]=dst_addr[next_loc-sizeof(__le16)-1-j];
			err=f2fs_decompress_delta_for_retrieve(basepage, tp, cur_ofs);
			if (err){
				printk(KERN_ALERT"decompress failed in inode retrieve\n");
				f2fs_put_dnode(&dn);
				f2fs_unlock_op(F2FS_I_SB(inode));
				if(PageLocked(basepage)) f2fs_put_page(basepage, 1);	
				else put_page(basepage);
				congestion_wait(BLK_RW_ASYNC, HZ/50);
				goto wait_unlock;
			}
			kfree(tp);
			SetPageUptodate(basepage);
		}
		err=f2fs_convert_inline_delta(&dn, basepage);/*perform page writeback*/
		if(err) {
			printk(KERN_ALERT"err in convert inline delta2:%d %d %d\n", inode->i_ino, current->pid, current->tgid);
			f2fs_put_dnode(&dn);
			f2fs_unlock_op(F2FS_I_SB(inode));
			if(PageLocked(basepage)) f2fs_put_page(basepage, 1);	
			else put_page(basepage);
			congestion_wait(BLK_RW_ASYNC, HZ/50);	
			goto wait_unlock;
		}	
		f2fs_put_dnode(&dn);
		f2fs_unlock_op(F2FS_I_SB(inode));
		if(PageLocked(basepage)) f2fs_put_page(basepage, 1);
	}
	f2fs_remove_dirty_inode(inode);
	/* this converted inline_data should be recovered. */
	set_inode_flag(inode, FI_APPEND_WRITE);
	clear_inode_flag(inode, FI_DELTA_TRUNCATING);
	F2FS_I(inode)->i_flags &= ~F2FS_DELTA_TRUNCATING;
	f2fs_balance_fs(F2FS_I_SB(inode), dn.node_changed);
	kfree(dst_addr);
	return 0;
}
int f2fs_decompress_delta_for_retrieve(struct page *page, char *tp, size_t dsize)
{
	int i,next_loc,ret=0;
	size_t clen;
	unsigned char c, ch, ch1;
	char *cbuf=NULL,* page_data=NULL,* new_data=NULL;
	struct inode *inode = page->mapping->host;
	if(inode==NULL) return 0;
	if(!PageLocked(page)) {
		printk(KERN_ALERT"lock page failed in f2fs_decompress_delta_for_retrieve:%d %d\n", inode->i_ino, page->index);
		return -1;
	}	

	//decompress
	if(tp!=NULL){
		clen=PAGE_SIZE;
		cbuf=f2fs_kzalloc(F2FS_I_SB(inode),clen,GFP_NOFS);	
		ret = lzo1x_decompress_safe(tp, dsize,
					cbuf, &clen);
		if (ret != LZO_E_OK) {
			printk_ratelimited("%sF2FS-fs (%s): lzo decompress failed, ret:%d\n",
					KERN_ERR, F2FS_I_SB(inode)->sb->s_id, ret);
			return -1;
		}		
	//merge delta to base
		page_data=kmap(page);
		new_data=NULL;
		new_data=kmalloc(PAGE_SIZE,GFP_NOFS);
		for(i=0;i<PAGE_SIZE;i++){
			ch=cbuf[i];
			ch1=page_data[i];
			new_data[i]=ch^ch1;
		}	
		memcpy(page_data,new_data,PAGE_SIZE);//restore new data	
		flush_dcache_page(page);
		kunmap(page);	
		kfree(cbuf);
		kfree(new_data);
	}
	return 0;
}

int f2fs_truncate_inline_delta(struct inode *inode, struct page *ipage, int from, int to, int delta_num, int delta_inline_size)
{
	int i, base=0;
	char *src_addr=NULL, *dst_addr=NULL;
	unsigned char c,ff1,ff2;
	__le32 *addr_array;
	struct f2fs_node *rn;

	f2fs_wait_on_page_writeback(ipage, NODE, true, true);
	dst_addr=kmalloc(PAGE_SIZE, GFP_NOFS);//cp inline to dst addr
	src_addr = inline_data_addr(inode, ipage);
	memcpy(dst_addr, src_addr, MAX_INLINE_DATA(inode));	
	for(i=from;i>to;i--)  
	{
		dst_addr[i]=0;
	}
	c=delta_num;
	dst_addr[872*sizeof(__le32)-1]=c;  
	ff1=delta_inline_size, ff2=delta_inline_size>>BITS_PER_BYTE;
	dst_addr[872*sizeof(__le32)-2]=ff1;
	dst_addr[872*sizeof(__le32)-3]=ff2;
	if(delta_num==0 || delta_inline_size==0)
	{
		if (IS_INODE(ipage) && f2fs_has_extra_attr(inode))
			base = get_extra_isize(inode);
		rn = F2FS_NODE(ipage);
		addr_array = blkaddr_in_node(rn);
		dst_addr[872*sizeof(__le32)-1]=0;
		dst_addr[872*sizeof(__le32)-2]=0;
		dst_addr[872*sizeof(__le32)-3]=0;	
		dst_addr[872*sizeof(__le32)-4]=0;
		dst_addr[872*sizeof(__le32)-5]=0;
		addr_array[base + 872] = cpu_to_le32(0);	
	}
	memcpy(src_addr, dst_addr, MAX_INLINE_DATA(inode));	

	set_page_dirty(ipage);
	kfree(dst_addr);
	return 0;
}
int f2fs_convert_inline_delta(struct dnode_of_data *dn, struct page *page)
{
	struct f2fs_io_info fio = {
		.sbi = F2FS_I_SB(dn->inode),
		.ino = dn->inode->i_ino,
		.type = DATA,
		.op = REQ_OP_WRITE,
		.op_flags = REQ_SYNC | REQ_PRIO,
		.page = page,
		.encrypted_page = NULL,
		.io_type = FS_DATA_IO,
	};
	struct node_info ni;
	int dirty, err;
	if(!PageLocked(page)) {
		printk(KERN_ALERT"lock page failed in f2fs_convert_inline_delta:%d %d\n", dn->inode->i_ino, page->index);
		return -1;
	}
	err = f2fs_reserve_block(dn, page->index);
	if (err)
		return err;

	err = f2fs_get_node_info(fio.sbi, dn->nid, &ni);
	if (err) {
		f2fs_truncate_data_blocks_range(dn, 1);
		return err;
	}

	fio.version = ni.version;
	f2fs_bug_on(F2FS_P_SB(page), PageWriteback(page));

	set_page_dirty(page);
	if(!PageLocked(page)) {
		printk(KERN_ALERT"lock page failed in f2fs_convert_inline_delta1:%d %d\n", dn->inode->i_ino, page->index);
		return -1;
	}
	/* clear dirty state */
	dirty = clear_page_dirty_for_io(page);

	/* write data page to try to make data consistent */
	set_page_writeback(page);
	ClearPageError(page);
	fio.old_blkaddr = dn->data_blkaddr;
	set_inode_flag(dn->inode, FI_HOT_DATA);
	f2fs_outplace_write_data(dn, &fio);
	f2fs_wait_on_page_writeback(page, DATA, true, true);
	if (dirty) {
		inode_dec_dirty_pages(dn->inode);
	}
	clear_inline_node(dn->inode_page);
	return 0;
}

bool f2fs_recover_inline_delta(struct inode *inode, struct page *npage)
{
	struct f2fs_sb_info *sbi = F2FS_I_SB(inode);
	struct f2fs_inode *ri = NULL;
	void *src_addr, *dst_addr;
	struct page *ipage;

	if (IS_INODE(npage))
		ri = F2FS_INODE(npage);

	if (is_inode_flag_set(inode, FI_INLINE_DELTA)) 
	{
		ipage = f2fs_get_node_page(sbi, inode->i_ino);
		f2fs_bug_on(sbi, IS_ERR(ipage));

		f2fs_wait_on_page_writeback(ipage, NODE, true, true);

		src_addr = inline_data_addr(inode, npage);
		dst_addr = inline_data_addr(inode, ipage);
		memcpy(dst_addr, src_addr, MAX_INLINE_DATA(inode));

		set_inode_flag(inode, FI_INLINE_DATA);
		set_inode_flag(inode, FI_DATA_EXIST);

		set_page_dirty(ipage);
		f2fs_put_page(ipage, 1);
	}
	return true;
}


/*
 * The maximum depth is four.
 * Offset[0] will have raw inode offset.
 */
static int f2fs_delta_get_node_path(struct inode *inode, long block,
				int offset[4], unsigned int noffset[4])
{
	const long direct_index = ADDRS_PER_INODE(inode);
	const long direct_blks = ADDRS_PER_BLOCK(inode);
	const long dptrs_per_blk = NIDS_PER_BLOCK;
	const long indirect_blks = ADDRS_PER_BLOCK(inode) * NIDS_PER_BLOCK;
	const long dindirect_blks = indirect_blks * NIDS_PER_BLOCK;
	int n = 0;
	int level = 0;

	noffset[0] = 0;

	if (block < direct_index) {
		offset[n] = block;
		goto got;
	}
	block -= direct_index;
	if (block < direct_blks) {
		offset[n++] = NODE_DIR1_BLOCK;
		noffset[n] = 1;
		offset[n] = block;
		level = 1;
		goto got;
	}
	block -= direct_blks;
	if (block < direct_blks) {
		offset[n++] = NODE_DIR2_BLOCK;
		noffset[n] = 2;
		offset[n] = block;
		level = 1;
		goto got;
	}
	block -= direct_blks;
	if (block < indirect_blks) {
		offset[n++] = NODE_IND1_BLOCK;
		noffset[n] = 3;
		offset[n++] = block / direct_blks;
		noffset[n] = 4 + offset[n - 1];
		offset[n] = block % direct_blks;
		level = 2;
		goto got;
	}
	block -= indirect_blks;
	if (block < indirect_blks) {
		offset[n++] = NODE_IND2_BLOCK;
		noffset[n] = 4 + dptrs_per_blk;
		offset[n++] = block / direct_blks;
		noffset[n] = 5 + dptrs_per_blk + offset[n - 1];
		offset[n] = block % direct_blks;
		level = 2;
		goto got;
	}
	block -= indirect_blks;
	if (block < dindirect_blks) {
		offset[n++] = NODE_DIND_BLOCK;
		noffset[n] = 5 + (dptrs_per_blk * 2);
		offset[n++] = block / indirect_blks;
		noffset[n] = 6 + (dptrs_per_blk * 2) +
			      offset[n - 1] * (dptrs_per_blk + 1);
		offset[n++] = (block / direct_blks) % dptrs_per_blk;
		noffset[n] = 7 + (dptrs_per_blk * 2) +
			      offset[n - 2] * (dptrs_per_blk + 1) +
			      offset[n - 1];
		offset[n] = block % direct_blks;
		level = 3;
		goto got;
	} else {
		return -E2BIG;
	}
got:
	return level;
}
#endif
