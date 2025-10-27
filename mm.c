/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"

#include <limits.h>

#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE   (1<<12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PREDP(bp) (*(void **)(bp))
#define SUCCP(bp) (*(void **)(bp + WSIZE))

typedef void * (*fit_policy_t)(size_t asize);

static char *free_listp;

static char *heap_listp;

static char *next_fit_p = NULL;

static void *coalesce_for_next_fit(void *bp);

static void *extend_heap(size_t words);

static void *find_fit(size_t asize, fit_policy_t fit_policy);

static void *next_fit(size_t asize);

static void place_for_next_fit(void *bp, size_t asize);

static void list_add(void *bp);

static void list_remove(void *bp);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1)
        return -1;

    PUT(heap_listp, 0);                         /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE); // heap_listp를 Prologue 페이로드로 이동

    free_listp = NULL;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize, next_fit)) != NULL) {
        place_for_next_fit(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place_for_next_fit(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce_for_next_fit(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *newptr;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    size_t copysize = GET_SIZE(HDRP(ptr)) - DSIZE;
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, oldptr, copysize);
    mm_free(oldptr);
    return newptr;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */

    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce_for_next_fit(bp);
}

static void list_add(void *bp) {
    PREDP(bp) = NULL;
    SUCCP(bp) = free_listp;
    if (free_listp != NULL) {
        PREDP(free_listp) = bp;
    }

    free_listp = bp;
}

static void list_remove(void *bp) {
    void *pred_bp = PREDP(bp);
    void *succ_bp = SUCCP(bp);

    if (pred_bp == NULL && succ_bp == NULL) {
        free_listp = NULL;
    } else if (pred_bp == NULL) {
        PREDP(succ_bp) = NULL;
        free_listp = succ_bp;
    } else if (succ_bp == NULL) {
        SUCCP(pred_bp) = NULL;
    } else {
        SUCCP(pred_bp) = succ_bp;
        PREDP(succ_bp) = pred_bp;
    }
}

static void *coalesce_for_next_fit(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    void *orig_bp = bp;
    void *next_bp = NEXT_BLKP(bp);

    if (prev_alloc && next_alloc) {
        /* Case 1 */
    } else if (prev_alloc && !next_alloc) {
        /* Case 2 */
        list_remove(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        /* Case 3 */
        list_remove(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        /* Case 4 */
        list_remove(PREV_BLKP(bp));
        list_remove(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    if ((next_fit_p != NULL) && (next_fit_p == orig_bp || next_fit_p == next_bp)) {
        next_fit_p = bp;
    }

    list_add(bp);
    return bp;
}

static void *next_fit(size_t asize) {
    void *bp;
    char *start_p;

    if (next_fit_p == NULL) {
        next_fit_p = free_listp;
    }
    start_p = next_fit_p;

    for (bp = start_p; bp != NULL; bp = SUCCP(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }

    for (bp = free_listp; bp != start_p; bp = SUCCP(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp; // 블록을 찾음
        }
    }

    return NULL; // 힙 전체를 탐색해도 적합한 블록이 없음
}

static void *find_fit(size_t asize, fit_policy_t fit_policy) {
    return fit_policy(asize);
}

static void place_for_next_fit(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    // [수정 1] bp를 제거하기 전에 다음 가용 블록(successor)을 저장
    void *succ_bp = SUCCP(bp);

    list_remove(bp); // 가용 리스트에서 제거

    if ((csize - asize) >= (2 * DSIZE)) {
        // [Case 1: 블록 분할]
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize-asize, 0));
        PUT(FTRP(next_bp), PACK(csize-asize, 0));
        list_add(next_bp);

        // 다음 탐색은 새로 생긴 가용 블록(next_bp)부터 시작
        next_fit_p = next_bp;

    } else {
        // [Case 2: 분할 없음]
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));

        // [수정 2] 다음 탐색을 메모리상 다음 블록(X)이 아닌,
        // 가용 리스트의 다음 블록(succ_bp)부터 시작
        // 만약 succ_bp가 NULL (꼬리)이었다면, 리스트의 처음으로 보냄
        next_fit_p = (succ_bp != NULL) ? succ_bp : free_listp;
    }
}