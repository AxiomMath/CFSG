module

public import Certificates.Data.CFSGNative.Mathieu.Check

public section

namespace CFSG.Sporadic.Mathieu.Native

open CFSG.Sporadic.Th.Native

@[expose] def m22Data (_ : Unit := ()) : Data where
  tA := #[12, 7, 15, 11, 4, 21, 16, 1, 9, 8, 13, 3, 0, 10, 14, 2, 6, 17, 18, 19, 20, 5]
  tB := #[21, 17, 20, 12, 11, 10, 14, 13, 8, 7, 6, 4, 1, 19, 5, 15, 18, 3, 16, 9, 0, 2]
  words :=
    #[[1], [2, 1, 2], [-3, -4, -4, -3, -4, 3, 4, 4, 3, -4], [-3, -4, 5, -3, 4, 3, -5, 4],
    [-6, -6], [-6, -5, 6, 6, 5, 6, 5], [8, 7, -8], [-7, 9, -8], [5, -10, 6, 5, 6, 5],
    [-9, 11, 9, 10, 11]]
  base := #[0, 1, 2, 3, 4]
  sizes := [22, 21, 20, 16, 3]
  k := 2
  pX := 2
  eX := 0
  pY := 5
  eY := 0
  pXY := 11
  eXY := 0

end CFSG.Sporadic.Mathieu.Native

