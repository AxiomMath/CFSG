module

public import Certificates.Data.CFSGNative.Mathieu.Check

public section

namespace CFSG.Sporadic.Mathieu.Native

open CFSG.Sporadic.Th.Native

@[expose] def m24Data (_ : Unit := ()) : Data where
  tA := #[3, 6, 16, 0, 12, 8, 1, 14, 5, 18, 17, 20, 4, 15, 7, 13, 2, 10, 9, 23, 11, 22, 21, 19]
  tB := #[3, 20, 8, 5, 17, 0, 6, 7, 14, 4, 10, 11, 16, 1, 2, 12, 15, 9, 23, 19, 13, 21, 18, 22]
  words :=
    #[[1], [2], [-3, 4], [5, 5, 5, 5, 4, 5, -3, -5, -5, -5, 4, 5, 3, -5, -4],
    [-5, 6, -5, -5, -5, -5, -6, -5], [-6, 7, 7, 6, 7, 6], [-6, -7, -8, 6, 6, 7, 6], [8, -9],
    [10, -8, 9, 8, -10, -8], [-10, 11, 10, -11, -10, -10], [12, 11, 10, 12, 11, -10, -10]]
  base := #[0, 1, 2, 3, 4, 5, 6]
  sizes := [24, 23, 22, 21, 20, 16, 3]
  k := 4
  pX := 2
  eX := 0
  pY := 3
  eY := 0
  pXY := 23
  eXY := 0

end CFSG.Sporadic.Mathieu.Native

