/* -----------------------------------------------------------
 *   
 *   Branch and bound for two dimensional star discrepancy
 *   subset selection
 *
 *   Support material for article
 *   Carola Doerr, Luís Paquete, "Star Discrepancy Subset Selection: Problem
 *   Formulation and Efficient Approaches for Low Dimensions"
 *
 *   version 0.1 -  January 2021
 * 
 *   input file format:
 *
 *   2 <n> <m>
 *   <x-coord of point 1> <y-coord of point 1>
 *   ...
 *   <x-coord of point n> <y-coord of point n>
 *
 *
 *   compile: gcc bb2D.c -O3
 *   run:     ./a.out < <input file>
 *
 * ----------------------------------------------------------- */

/* -----------------------------------------------------------
 *  includes							
 * ----------------------------------------------------------- */

#include <stdlib.h>
#include <stdio.h>
#include <float.h>
#include <string.h>
#include <limits.h>
#include <time.h>
#include <math.h>


/* -----------------------------------------------------------
 *  macros
 * ----------------------------------------------------------- */

#define min(a,b) (((a)<(b))?(a):(b))
#define max(a,b) (((a)>(b))?(a):(b))
#define Abs(a)    ((a) < 0 ? -(a) : (a))

/*-----------------------------------------------------------
 *  constants
 * ----------------------------------------------------------- */

#define MAXN		256
#define INFEASIBLE       -1
#define COMPLETE         -1
#define BACKTRACK        -1

/* -----------------------------------------------------------
 *  variables and data structures 
 * -----------------------------------------------------------  */

int n;				/* number of points 		*/
int k;				/* constraint			*/

struct point {			/* pointers to data		*/
   double x;			/* x-coord			*/	
   double y;			/* y-coord			*/
   int i;			/* x-position in the grid	*/
   int j;			/* y-position in the grid 	*/
};  

struct node {			/* solution representation 	*/
   double v;			/* star discrepancy value 	*/
   int k;			/* cardinality 			*/
   int p[MAXN];			/* points in the solution 	*/
};

struct point p[MAXN];		/* points struct		*/	
int px[MAXN];			/* points sorted in x		*/
int py[MAXN];			/* points sorted in y		*/

double gh[MAXN][MAXN];		/* area for each grid point	*/
int g0d[MAXN][MAXN];		/* pre-computed information 	*/
int g1d[MAXN][MAXN];
int gdd[MAXN][MAXN];
double divk[MAXN];		

struct node knode;		/* current solution		*/
struct node bnode;		/* best solution 		*/

double bnd1[MAXN];		/* lower bounds			*/
double bnd2[MAXN];

clock_t end, start;		/* timing variables		*/
double cput;


/* -----------------------------------------------------------
 *  sorting functions 
 * -----------------------------------------------------------  */

int comparexy (const void * a, const void * b) {
   
   const struct point pi = *(struct point *) a;    
   const struct point pj = *(struct point *) b;

   if (pi.x < pj.x) return -1;
   if (pi.x > pj.x) return 1;

   return 0;
}

int comparex (const void * a, const void * b) {

   const int i = *(int *) a;    
   const int j = *(int *) b;

   if (p[i].x < p[j].x) return -1;
   if (p[i].x > p[j].x) return  1;
   if (p[i].y < p[j].y) return -1;
   if (p[i].y > p[j].y) return  1;
   return 0;
}

int comparey (const void * a, const void * b) {

    const int i = *(int *) a;    
    const int j = *(int *) b;

    if (p[i].y < p[j].y) return -1;
    if (p[i].y > p[j].y) return  1;
    if (p[i].x < p[j].x) return -1;
    if (p[i].x > p[j].x) return  1;
    return 0;
}

/* -----------------------------------------------------------
 * bounds   
 * -----------------------------------------------------------  */

double lb1A(int l, int c) {
	
	int j;
	int ix, iy, jx, jy;
	double vmax = 0;
	
	if (knode.k == 0)
		return 0;
	if (c == 0){
		for (j = 0; j < knode.k; j++){
			jy = p[knode.p[j]].j;
			vmax = max(vmax,gh[n][jy]-divk[min(k,g1d[n][jy]+gdd[l][jy])]);
		}
		vmax = max(vmax, 1.0 - divk[min(k, g1d[n][n] + gdd[l][n])]);
	}
	if (c == 1){
		ix = p[knode.p[knode.k-1]].i;
		iy = p[knode.p[knode.k-1]].j;
		vmax = max(vmax, gh[ix][iy] - divk[min(k, g1d[ix][iy])]);
		for (j = 0; j < knode.k-1; j++){
			jx = p[knode.p[j]].i;
			jy = p[knode.p[j]].j;
			vmax = max(vmax,gh[ix][jy]-divk[min(k,g1d[ix][jy])]);
			vmax = max(vmax,gh[jx][iy]-divk[min(k,g1d[jx][iy])]);
		}
		vmax = max(vmax, gh[ix][n] - divk[min(k, g1d[ix][n])]);
		vmax = max(vmax, gh[n][iy] - divk[min(k, g1d[n][iy] + gdd[l][iy])]);
	}
	return max(bnd1[l-1],vmax);
}

double lb2A(int l, int c) {
	
	int j;
	int ix, iy, jx, jy;
	double vmax = -DBL_MAX;

	if (knode.k == 0)
		return 0;
	if (c == 1){
		ix = p[knode.p[knode.k-1]].i;
		iy = p[knode.p[knode.k-1]].j;
		vmax = max(vmax,-gh[ix][iy]+divk[g0d[ix][iy]]);
		
		for (j = 0; j < knode.k-1; j++){
			jx = p[knode.p[j]].i;
			jy = p[knode.p[j]].j;
			vmax = max(vmax,-gh[jx][iy]+divk[g0d[jx][iy]]);
			vmax = max(vmax,-gh[ix][jy]+divk[g0d[ix][jy]]);
		}
	}
	return max(bnd2[l-1],vmax);
}


/* -----------------------------------------------------------
 * update grid information 
 * -----------------------------------------------------------  */

void update(int l, int b) {
 	
	int i, j;
	int ix, iy;

	ix = p[l].i;
	iy = p[l].j;
	
	if (b == 1) {
		for (i = ix+1; i <= n; i++) 
			for (j = iy+1; j <= n; j++) 
				g1d[i][j]++;
		for (i = ix; i < n; i++) 
			for (j = iy; j < n; j++) 
				g0d[i][j]++;
	}
	else if (b == 0){
		for (i = ix+1; i <= n; i++)
			for (j = iy+1; j <= n; j++)
				g1d[i][j]--;
		for (i = ix; i < n; i++)
			for (j = iy; j < n; j++)
				g0d[i][j]--;
	}
}


/* -----------------------------------------------------------
 * compute star discrepancy value   
 * -----------------------------------------------------------  */

double starc(struct node nd) {
	
	int i, j;
	int ix, iy, jx, jy;
	double vmax0 = -DBL_MAX;
	double vmax1 = -DBL_MAX;
	
	for (i = 0; i < nd.k; i++) {
		ix = p[nd.p[i]].i;
		iy = p[nd.p[i]].j;
		for (j = i; j < nd.k; j++) {
			jx = p[nd.p[j]].i;
			jy = p[nd.p[j]].j;
			vmax1 = max(vmax1,   gh[ix][jy] - divk[g1d[ix][jy]]);
			vmax1 = max(vmax1,   gh[jx][iy] - divk[g1d[jx][iy]]);
			vmax0 = max(vmax0, - gh[ix][jy] + divk[g0d[ix][jy]]);
			vmax0 = max(vmax0, - gh[jx][iy] + divk[g0d[jx][iy]]);
		}
		vmax1 = max(vmax1,   gh[ix][n] - divk[g1d[ix][n]]);
		vmax1 = max(vmax1,   gh[n][iy] - divk[g1d[n][iy]]);
	}
	vmax1 = max(vmax1, 1.0 - divk[g1d[n][n]]);
	return max(vmax0,vmax1);
}


double star(struct node nd, int l, int c) {
	
	int i, j;
	int ix, iy, jx, jy;
	double vmax1 = -DBL_MAX;
	double vmax2 = lb2A(l, c);
	
	for (i = 0; i < nd.k; i++) {
		ix = p[nd.p[i]].i;
		iy = p[nd.p[i]].j;
		for (j = i; j < nd.k; j++) {
			jx = p[nd.p[j]].i;
			jy = p[nd.p[j]].j;
			vmax1 = max(vmax1,   gh[ix][jy] - divk[g1d[ix][jy]]);
			vmax1 = max(vmax1,   gh[jx][iy] - divk[g1d[jx][iy]]);
		}
		vmax1 = max(vmax1,   gh[ix][n] - divk[g1d[ix][n]]);
		vmax1 = max(vmax1,   gh[n][iy] - divk[g1d[n][iy]]);
	}
	vmax1 = max(vmax1, 1.0 - divk[g1d[n][n]]);

	return max(vmax1,vmax2);
}


/* -----------------------------------------------------------
 * greedy heuristic   
 * -----------------------------------------------------------  */

double heur1() {
	int i, j, l, idx=0;
	struct node hnode;
	int found;
	double mini;
	
	hnode.k = 0;
	for (i = 0; i < k; i++) {
		hnode.k++;
		mini = DBL_MAX;
		for (j = 0; j < n; j++) {
			found = 0;
			for (l = 0; l < i; l++) 
				if (hnode.p[l] == j)
					found = 1;
			if (found == 0)	{
				hnode.p[i] = j;
				update(hnode.p[i],1);
				hnode.v = starc(hnode);
				if (hnode.v <= mini) {
					mini = hnode.v;
					idx = j;
				}
				update(hnode.p[i],0);
			}
		}
		hnode.p[i] = idx;
		update(hnode.p[i],1);
	}
	hnode.v = starc(hnode);
	for (i = 0; i < k; i++) 	
		update(hnode.p[i],0);
	return hnode.v;
}


/* -----------------------------------------------------------
 * bounds and feasibility   
 * -----------------------------------------------------------  */

int bounds(int i, int c) {
	if ((i > n) || (n - i < k - knode.k))
		return INFEASIBLE;
	
	else if (knode.k == k) {
		knode.v = star(knode, i, c);
		if (bnode.v > knode.v) {
			bnode.v = knode.v;
			memcpy(bnode.p, knode.p, sizeof(knode.p));
			end = clock();
		}
		return COMPLETE; 
	}
	
	else {
		bnd1[i] = lb1A(i,c);
		if (bnode.v < bnd1[i])
			return INFEASIBLE;
		bnd2[i] = lb2A(i,c);
		if (bnode.v < bnd2[i]) 
			return INFEASIBLE;
	}
	return i;
}


/* -----------------------------------------------------------
 *  branch and bound  
 * -----------------------------------------------------------  */

void bnb(int i, int c) {
	i = bounds(i, c);
	if (i != BACKTRACK) {
	
		knode.p[knode.k] = i;
		update(i, 1);
		knode.k++;
		bnb(i+1, 1);
		
		knode.k--;
        	update(i, 0);
		knode.p[knode.k] = -1;
		bnb(i+1, 0);
     	}
    	return;
}

/* -----------------------------------------------------------
 *  main  
 * -----------------------------------------------------------  */

int main(int argc, char *argv[]){
	int i, j, l, d;
    	double x, y;

	start = clock();
	bnode.v = knode.v = DBL_MAX;

	/* reading input data */
	scanf("%d %d %d", &d, &n, &k);
    	for (i=0; i<n; i++) {
        	scanf("%lf %lf", &x, &y);
	    	p[i].x = x; p[i].y = y; 
		knode.p[i] = bnode.p[i] = -1;
	}

	/* sorting in x */
	qsort(p, n, sizeof(p[0]), comparexy);

	/* define grid points */
	for (i=0; i<n; i++) {
		px[i] = i; py[i] = i;
	}
	qsort(px, n, sizeof(px[0]), comparex); 
	qsort(py, n, sizeof(py[0]), comparey); 
	for (i=0; i<n; i++){
		for (j=0; j<n; j++) {
			if (px[j] == i)
				p[i].i = j;
			if (py[j] == i)
				p[i].j = j;
		}
	}

	/* pre-computed information */
	memset(gdd,0,sizeof(gdd));
	memset(g1d,0,sizeof(g1d));
	memset(g0d,0,sizeof(g1d));

	/* hypervolume of each grid point */
	for (i=0; i<n; i++){
		for (j=0; j<n; j++)
			gh[i][j] = p[px[i]].x*p[py[j]].y;
		gh[i][n] = p[px[i]].x;
		gh[n][i] = p[py[i]].y;
	}
	gh[n][n] = 1;


	/* pre-computed division */
	for (i=0; i<=k; i++)
		divk[i] = (double) i / k;
	
	/* pre-computed lower bounds */
	for (l=n-1; l>=0; l--) { 
		memcpy(gdd[l],gdd[l+1],sizeof(gdd[l+1]));
		for (j = p[l].j+1; j<=n; j++)
			gdd[l][j] ++;
	}
	memset(bnd1,-1,sizeof(bnd1));
	memset(bnd2,-1,sizeof(bnd2));

	/* greedy heuristic */
	bnode.v = heur1();
	
	bnb(0,1);
	
	end = clock();
	cput = ((double) (end - start)) / CLOCKS_PER_SEC;
	printf("%.6lf %lf\n",bnode.v, cput);
	
	return 0;
}

/* -----------------------------------------------------------
 * the end 
 * -----------------------------------------------------------  */





