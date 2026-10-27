module

public import CFSG.Sporadic.Schreier.M23Gens
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates

@[expose] def m23Words : List (List ℤ) :=
  [[-1, 2, 1, -2, 1], [-2, 3, 2], [-2, -1, 4, 2], [5, -4, -1, 5, 1, 2], [-1, 6, 1],
    [-6, 7, -3, -5, -7, -1, 5, 4, 2], [8, -6, -7, -6, -8, -1, 8, 1], [-1, 9, 1],
    [-7, -10, -1, 8, 1], [8, -11, -6, -9, -1, -11, 1], [-12, -1, 12, 1],
    [-12, -11, -6, 7, 5, -10, -1, 5, 4, 2]]

@[expose] def m23Certificate : RawSchreierDatum 23 :=
  certificate (by decide) [m23PermA, m23PermB] m23Words #v[0, 1, 2, 3, 4, 5] (by decide)

end CFSG.Sporadic.Schreier
