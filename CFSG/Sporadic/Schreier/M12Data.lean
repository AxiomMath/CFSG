module

public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def m12Words : List (List ℤ) :=
  [[-2, 1, 2], [-1, 3, 1], [-2, 3, 2], [-2, 4, 2], [-1, -2, 6, 2, 1], [-3, 2, 7, -2],
    [-3, -7, -1, -8, 4, -2], [-7, -4, -1, -9, -2, 1], [-6, -10, -8, -1, -10, -9, 1],
    [-6, -8, 9, -4, -6, -1, -10, 6, 2]]

@[expose] def m12Certificate : RawSchreierDatum 12 :=
  certificate (by decide) [m12gA, m12gB] m12Words #v[0, 1, 2, 3, 4] (by decide)

end CFSG.Sporadic.Schreier
