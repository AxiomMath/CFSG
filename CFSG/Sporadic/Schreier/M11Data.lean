module

public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def m11Words : List (List ℤ) :=
  [[-2, -1, 2, 1, 2], [3, -2, -1, -3, 2], [-3, -1, -3, -4, -2, -2, -3, 4, 3, 2],
    [-3, -1, -3, -1, -2, -5, 1, -2]]

@[expose] def m11Certificate : RawSchreierDatum 11 :=
  certificate (by decide) [m11gA, m11gB] m11Words #v[0, 1, 2, 3] (by decide)

@[expose] def m11Elements : List (Equiv.Perm (Fin 11)) := (enumeration m11Certificate).map tab

end CFSG.Sporadic.Schreier
