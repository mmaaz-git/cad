# Cylindrical algebraic decomposition in Python

## Background

This is an implementation of cylindrical algebraic decomposition (CAD) in pure Python, based on SymPy as the computer algebra backend. CAD is a fundamental algorithm: it can test the consistency of a semialgebraic set, i.e., a system defined by Boolean combinations of multivariate polynomials. This makes it extremely general and powerful, but also means it scales poorly. Currently, there are few implementations of CAD available. There is one in Mathematica; there is also something called QEPCAD, developed by Christopher W. Brown, who was key in the development of CAD; as well, satisfiability modulo theories (SMT) solvers like Z3 by Microsoft also implement it as the theory solver for nonlinear real arithmetic (NRA). However, there is no implementation right now in pure Python. 

I am currently working to have it integrated into SymPy, which is my ultimate goal. This repo is sort of a placeholder until that is accomplished. The `cad.py` file contains everything you need. There may be bugs, some due to how SymPy handles polynomials. As of writing (Aug 9, 2024), I'm currently ironing these out as I integrate this into SymPy.

CAD decomposes $\mathbb{R}^n$ into *cells* over which each polynomial is sign-invariant, returning a *sample point* in each of these cells. Then, the consistency of the system can be checked over each of these cells just by plugging in the sample point representing it. In this way, we can find a satisfying point for a semialgebraic set, or return that none exists. That's what this CAD implementation does. There is a further step in CAD which goes beyond just satisfiability, and actually constructs a *solution formula* that describes the semialgebraic set; this is required to perform quantifier elimination over the reals. I have not implemented this yet. To my knowledge, only Mathematica and QEPCAD do. That step is quite complicated, and is pretty much only covered in the PhD thesis of Christopher W. Brown.

## Examples

The main interface is `solve_poly_system_cad` which takes a list of polynomials and a list of variables. The other functions are all background to this. By default, it returns a single satisfying point, if it exists, otherwise an empty list.

```
>>> import cad
>>> from sympy.abc import x,y,z
>>> from sympy import *
>>> 
>>> cad.solve_poly_system_cad([x**2 + 1 > 0], [x])
[{x: 0}]
>>> 
>>> cad.solve_poly_system_cad([x*y**2 - 3 < 1, x**5 + x**3 - x*y + 5 < 0], [x,y])
[{y: -2, x: -2}]
>>> 
>>> cad.solve_poly_system_cad([x**3 + y**2 + z**5 - z**3 > 3, x+y+z<1], [x,y,z])
[{z: -3, y: -16, x: 0}]
>>> 
>>> cad.solve_poly_system_cad([-x**2-1 > 0], [x])
[]
>>>
```

As you can see, it returns satisfying points for the first three systems. Predictably, the fourth system, which is a quadratic always lying below the x-axis, is not satisfiable.

