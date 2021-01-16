# StarDSS
Branch and bound for two dimensional star discrepancy subset selection

Support material for article
Carola Doerr, Luís Paquete, "Star Discrepancy Subset Selection: Problem
Formulation and Efficient Approaches for Low Dimensions"

version 0.1 -  January 2021

input file format:

2 <n> <m>

<x-coord of point 1> <y-coord of point 1>

...

<x-coord of point n> <y-coord of point n>

compile: gcc bb2D.c -O3

run:     ./a.out < <input file>
