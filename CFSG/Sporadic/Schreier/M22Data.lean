module

public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def m22Words : List (List ℤ) :=
  [[2, 1, -2], [-1, -3, 1, 3, 1], [-2, -4, 1, 2, 1], [-2, -2, 5, 2], [6, -1, -2, -6, 1],
    [-5, -6, -1, -7, 2, 2], [-3, -7, -1, -7, 5, 2], [-8, 7, -6, -9, -1, -8, 9, 2],
    [-8, -10, -5, -10, -1, -8, 9, 2], [-7, -7, -3, -8, -1, -11, 7, 2],
    [-10, 12, -9, -5, -10, -1, 12, 8, 2]]

@[expose] def m22Certificate : RawSchreierDatum 22 :=
  certificate (by decide) [m22gA, m22gB] m22Words #v[0, 1, 2, 3, 4] (by decide)

end CFSG.Sporadic.Schreier
