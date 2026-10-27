module

public import Certificates.Data.CFSGNative.Mathieu.Check

public section

namespace CFSG.Sporadic.Mathieu.Native

open CFSG.Sporadic.Th.Native

@[expose] def m11Data (_ : Unit := ()) : Data where
  tA := #[0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3]
  tB := #[3, 4, 7, 2, 5, 8, 6, 0, 1, 9, 10]
  words :=
    #[[2], [1, 2, 1, 2, 1, 2], [4, 3, 4, 4], [5, -4, 5, -3, 4, 4], [-5, -6, 5, 5],
    [-5, 6, -3, 7, -3, 4, 4], [6, 8, -7, 6]]
  base := #[0, 1, 2, 3]
  sizes := [11, 10, 9, 8]
  k := 2
  pX := 2
  eX := 1
  pY := 11
  eY := 0
  pXY := 11
  eXY := 0

end CFSG.Sporadic.Mathieu.Native

