module

public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.ClassSum

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def m24Words : List (List ℤ) :=
  [[-1, 2], [-1, -3, -3, -3, 2, 3, 1], [-3, -3, 2, 4, 4, 3, 1], [5, -3, -5, -1, -4, -5, -2],
    [-4, 6, -4, 5, -4, 5, -3, -6, 3, -1, -3, 4, -2], [-4, -7, 5, -3, -3, -1, 7, 1],
    [-8, -4, -6, -5, -8, 3, -5, -1, 8, 1], [-7, -6, 4, -5, 7, 5, -3, -3, 4, -1, -7, 1],
    [-10, -7, -7, -9, -4, -6, -5, -10, -3, -3, 6, -1, 10, 1]]

@[expose] def m24Certificate : RawSchreierDatum 24 :=
  certificate (by decide) [m24gA, m24gB] m24Words #v[0, 1, 2, 3, 4, 5, 6] (by decide)

end CFSG.Sporadic.Schreier
