/* 
 * Simple allocator based on explicit free lists, first fit placement, 
 * and boundary tag coalescing.
 * Blocks must be aligned to doubleword (8 byte) boundaries.
 * Minimum block size is 16 bytes. 
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
#define NEXT_FITx

/* begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
/*The small chunksize allows us to allocate only the required amount of bytes 
and thus saves us a lot on unused heap space at the end of the trace*/
#define CHUNKSIZE (1<<8) /* Extend heap by this amount (bytes) */ 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))  
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)               
#define GET_ALLOC(p) (GET(p) & 0x1)                

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/*used to convert between pointers and offsets for the explicit list*/
#define GET_ADDR_INDEX(bp) (unsigned)((char *)bp - (char *)heap_listp)
#define GET_ADDR(index) (((char *)heap_listp) + index)
/*This macro aligns a size by DSIZE and 
adds an extra 8 bytes for the header and the footer*/
#define ALIGN(size) ((size + 15) & ~0x7)

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  
unsigned freelist;

/* Function prototypes for internal helper routines */
/*used to extend the heap*/
inline static void *extend_heap(size_t words);
/*makes a block allocated and puts the remainder of the block back*/
inline static void place(void *bp, size_t asize);
/*finds a block that has atleast asize bytes after being aligned*/
inline static void *find_fit(size_t asize);
/*coalesces multiple blocks*/
inline static void *coalesce(void *bp);
/*these functions are used to add/remove from the freelist*/
inline static void removeFromFreeList(char *bp);
inline static void addToFreeList(char *bp);
/*these functions are used for debugging*/
inline static void printblock(void *bp); /*prints a block*/ 
inline static void checkblock(void *bp); /*checks block's consistency*/
inline static void checkFreeList(); /*checks consistency of the freelist*/

/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk(2*DSIZE)) == (void *)-1) 
		return -1;
	PUT(heap_listp, 0);                          /* Alignment padding */
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2*WSIZE);                 
	freelist = 0;

	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
		return -1;
	return 0;
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
inline static void *extend_heap(size_t words) 
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
	if ((long)(bp = mem_sbrk(size)) == -1)  
		return NULL;    

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */ 
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 
	/* Initialize and Coalesce */
	PUT(bp, 0);
	PUT(bp+WSIZE, 0);
	bp = coalesce(bp);
	addToFreeList( bp );
	return bp;
}


/* 
 * mm_free - Free a block 
 */
void free(void *bp)
{
	if(bp == 0) 
		return;

	size_t size = GET_SIZE(HDRP(bp));

/*new free block initialized*/
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(bp, 0);
	PUT(bp + WSIZE, 0);
/*coalescing and then adding it to the freelist*/
	bp = coalesce(bp);
	addToFreeList(bp);
}
/*
 *This method adds a given block to the freelist.
 *It takes in the pointer to the first byte of the payload, 
 *i.e. right after the header.
 */
inline static void addToFreeList(char *bp){
/*Putting the free block at the beginning of the freelist*/
	PUT(bp, 0); /*set previous pointer to be zero*/
	PUT(bp + WSIZE, freelist);
/*connecting the prev pointer of the initial first node 
  to bp*/ 
	if(freelist != 0)
		PUT(GET_ADDR(freelist) , GET_ADDR_INDEX(bp));
/*setting freelist to bp*/
	freelist = GET_ADDR_INDEX(bp);
	return;
}

/*
 *This method removes a given block from the freelist.
 *It takes in the pointer to the first byte of the payload, 
 *i.e. right after the header.
 */
inline static void removeFromFreeList(char *bp){
/*storing the previous and the next ptr*/
	char* ptr = bp + WSIZE;
	unsigned prev = GET(bp);
	unsigned next = GET(ptr);
	if(prev != 0 && next != 0){ /*case 1:*/
		PUT(((char *)GET_ADDR(prev) + WSIZE), next); 	
		PUT((GET_ADDR(next)), prev);
	}
	else if(prev == 0 && next != 0){ /*case 2:*/	
		freelist = next;
		PUT(GET_ADDR(freelist) , 0);
	}	
	else if(prev != 0 && next == 0){ /*case 3:*/	
		PUT(((char *)GET_ADDR(prev) + WSIZE), 0);
	}
	else if(prev == 0 && next == 0){ /*case 4:*/
		freelist = 0;
	}
}
/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
inline static void *coalesce(void *bp) 
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {            /* Case 1 */
/*Nothing to be done here*/
	}
/*only the next block is free so add them together.*/
	else if (prev_alloc && !next_alloc) {      /* Case 2 */
	/*remove next block from the free list*/
		removeFromFreeList(NEXT_BLKP(bp)); 
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
/*only the previous block is free so add them together*/
	else if (!prev_alloc && next_alloc) {      /* Case 3 */
		bp = PREV_BLKP(bp);
/*remove prev block from the free list*/
		removeFromFreeList(bp); 
		size += GET_SIZE(HDRP(bp));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
	else{                                     /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		removeFromFreeList(NEXT_BLKP(bp));
		bp = PREV_BLKP(bp);
		removeFromFreeList(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
	return bp;
}
/*
 * mm_realloc - Naive implementation of realloc
 */
void *realloc(void *ptr, size_t size)
{
	size_t oldsize, asize;
	void *newptr;
	
	/* If oldptr is NULL, then this is just malloc. */
	if(ptr == NULL) {
		return malloc(size);
	}
	
	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0) {
		free(ptr);
		return 0;
	}
	
	oldsize = GET_SIZE(HDRP(ptr));
	asize = ALIGN(size);
	/*oldsize is larger than or equal to asize need to shrink block*/
	if(oldsize >= asize){
		/*if difference to be shrunk is less than 16 bytes,
			 then can't shrink*/
		if(oldsize - asize < (2*DSIZE)){
			return ptr;
		}
		/*else we shrink the block*/
		else{
			PUT(HDRP(ptr), PACK(asize,1));
			PUT(FTRP(ptr), PACK(asize,1));
		/*store back the remaining space in the freelist*/
			newptr = NEXT_BLKP(ptr);
			PUT(HDRP(newptr), PACK(oldsize-asize , 0));
			PUT(FTRP(newptr), PACK(oldsize-asize , 0));
			PUT(newptr , 0);
			PUT(newptr + WSIZE, 0);
			coalesce(newptr);
			addToFreeList(newptr);
			dbg_printf( "realloc() -> %p\n\n", ptr);
			return ptr;
		}
	}
	else if(asize > oldsize){
		newptr = malloc(asize);
		/* If realloc() fails the original block is left untouched  */
		if(!newptr) {
			return 0;
		}
		/* Copy the old data. */
		memcpy(newptr, ptr, oldsize);
		/* Free the old block. */
		free(ptr);
		return newptr;
	}
	return 0;
}
/*
 * This method basically calls malloc and then initializes everything to 0.
 */
void *calloc (size_t nmemb, size_t size)
{
/*evaluates the total number of bytes and calls malloc*/
  size_t bytes = nmemb * size;
  void *newptr;
  newptr = malloc(bytes);
  if(newptr != NULL)
	memset(newptr, 0, bytes);
  return newptr;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
void *malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	char *bp;      
	dbg_printf("malloc( %lu )\n", size);
	/* Ignore spurious requests */
	if (size == 0)
		return NULL;
	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)   
		asize = 2*DSIZE;    
	else
		asize = ALIGN(size);
	/* Search the free list for a fit */
	if ((bp = find_fit(asize)) != NULL) {  
		place(bp, asize);
		return bp;
	}
	/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize,CHUNKSIZE);     
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
		return NULL;                             
	place(bp, asize);
	return bp;
} 
/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
inline static void place(void *bp, size_t asize)
{
	char* nextbp;
	size_t csize = GET_SIZE(HDRP(bp));   
	removeFromFreeList(bp);
	if((csize-asize)>= 2*DSIZE)
	{		
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		nextbp = NEXT_BLKP(bp); 
		PUT(HDRP(nextbp), PACK(csize-asize, 0)); 
		PUT(FTRP(nextbp), PACK(csize-asize, 0));	
		addToFreeList(nextbp);
	}
	else
	{
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}

}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
inline static void *find_fit(size_t asize)
{
	char* ptr;
	unsigned val=freelist;
	size_t blk_size;
/*loops through the freelist and finds the first fit.*/
	while(val != 0 ){
		ptr = GET_ADDR(val);
		blk_size = GET_SIZE(HDRP(ptr));
		if( blk_size >= asize )
			return ptr;
		val = GET( ptr + WSIZE);
	}
	return NULL;
}
/*
 * prints a block given the pointer to the payload
 */
inline static void printblock(void *bp) 
{
	size_t hsize, halloc, fsize, falloc;
	void *pred, *succ;
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));

	size_t p, s;
	p = GET( bp );
	s = GET( bp + WSIZE );
	pred = p ? GET_ADDR( p ) : NULL;
	succ = s ? GET_ADDR( s ) : NULL;

	if (hsize == 0) {
		printf("%p: epilogue block\n", bp);
		return;
	}
	printf("%p -> header = [%lu:%c], footer = [%lu:%c]\n", bp, 
			hsize, (halloc ? 'a' : 'f'), 
			fsize, (falloc ? 'a' : 'f'));
	if(halloc == 0)
		printf( "\tpred = [%p], succ = [%p]\n", pred, succ );
}

/*
 *checks the consistency of a block
 */
inline static void checkblock(void *bp) 
{
/*checking for out of bounds memory*/
	if((size_t)bp > ((size_t)mem_heap_hi())-3)
		printf("using memory out of bounds!!\n");
/*checking for alignment*/
	if ((size_t)bp % 8)
		printf("Error: %p is not doubleword aligned\n", bp);
/*checking if the header matches the footer */
	if (GET(HDRP(bp)) != GET(FTRP(bp))){
		printf("Error: header does[%u] not match footer[%u]\n",
			 GET(HDRP(bp)), GET(FTRP(bp)));
	}
	if(GET_ALLOC(HDRP(bp)) == 0){
		if(GET_ALLOC(HDRP(PREV_BLKP(bp))) == 0
			||  GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0)
			printf("this block has not been coalesced!!\n");
	}
}
/*
 * checkheap - runs through the heap to 
 *	check for various inconsistencies.
 */
void mm_checkheap(int verbose) 
{
	char *bp = heap_listp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);
/*check if the prologue block is fine*/
	if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) 
		|| !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);
	int i=0;
/*check consistency of each block*/
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { 
		if(verbose)
			printblock(bp);
		checkblock(bp);
		i++;
	}
/*run the freelist consistency checker*/
	checkFreeList();
/*checks if the epilogue block is good*/
	if( bp != mem_heap_lo() + mem_heapsize() )
		printf( "wrong epilogue pointer\n" );
	if (verbose)
		printblock(bp);
	if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
		printf("Bad epilogue header\n");
}
/*
 *looks for inconsistencies in the freelist
 */
inline static void checkFreeList(){
	char* a;
	if(freelist == 0){
		printf("empty freelist\n");
		return;
	}
	int i = 1, j=0;
	a = GET_ADDR(freelist);
	if(GET(a)!=0)
		printf("beginning of the list is messed up!\n");
    while( GET(a + WSIZE) != 0){
		/*checks if the freelist has an allocated block*/
	if( GET_ALLOC( HDRP( a ) ) == 1 )
		printf("Allocated block found in the freelist\n" );
	if((size_t)GET_ADDR(GET(a)) < (size_t)(mem_heap_lo()) 
	     || (size_t)GET_ADDR(GET(a)) > (size_t)(mem_heap_hi())
	     || (size_t)GET_ADDR(GET(a + WSIZE)) < (size_t)(mem_heap_lo()) 
	     || (size_t)GET_ADDR(GET(a + WSIZE)) > (size_t)(mem_heap_hi()))
			printf("out of bounds memory in the freelist\n");
		/*next's prev ptr == this block*/
		else if(GET(GET_ADDR(GET(a + WSIZE))) != GET_ADDR_INDEX(a)){
			printblock(a);
			printf("NEXT ptr/ PREV ptr of next block are wrong!\n");
		}
		a = GET_ADDR( GET(a+WSIZE));
		i++;
	}
	for (a = heap_listp; GET_SIZE(HDRP(a)) > 0; a = NEXT_BLKP(a)) {
               	if(GET_ALLOC(HDRP(a)) == 0)
			j++;
        }
     if((i-1) != j){
	printf("The number of free blocks counted through the freelist\
		don't match the number of the free blocks\
			 counted by traversing the heap\n");
	}

}
