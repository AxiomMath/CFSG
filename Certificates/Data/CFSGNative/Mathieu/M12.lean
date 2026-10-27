module

public import Certificates.Data.CFSGNative.Mathieu.Check

public section

namespace CFSG.Sporadic.Mathieu.Native

open CFSG.Sporadic.Th.Native

@[expose] def m12Data (_ : Unit := ()) : Data where
  tA := #[3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5]
  tB := #[7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]
  words :=
    #[[1], [2], [-3, -4, 3, 4, 3], [4, -5, 3, -4, 3], [-5, -6, -5, 6, 5, 6, 5], [-3, -4, 7, 4, 3],
    [-5, -6, -8, 5, 8, 6, 5], [-8, 9, 8], [-7, -9, -6, -9, 6, 8, 6, 5], [-4, -10, 5, 4, 3],
    [-8, 12, -7, 11, 7, -12]]
  base := #[0, 1, 2, 3, 4]
  sizes := [12, 11, 10, 9, 8]
  k := 4
  pX := 2
  eX := 0
  pY := 3
  eY := 0
  pXY := 11
  eXY := 0

end CFSG.Sporadic.Mathieu.Native

