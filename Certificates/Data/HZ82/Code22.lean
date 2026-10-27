module

public import Certificates.Data.CFSGNative.Mathieu.Check

public section

namespace CFSG.Quasithin.H.Code22.Native

open CFSG.Sporadic.Mathieu.Native CFSG.Sporadic.Th.Native

@[expose] def l22Data : Data where
  tA := #[0, 1, 5, 7, 6, 2, 3, 4, 10, 19, 9, 16, 15, 22, 12, 21, 20, 13, 23, 14, 17, 8, 18, 11]
  tB := #[0, 1, 6, 7, 3, 2, 5, 4, 8, 9, 14, 15, 11, 10, 13, 12, 20, 21, 18, 19, 23, 22, 17, 16]
  words :=
    #[[1],
    [2],
    [-3, -4],
    [5, 5, -4, -3, -4, -5, -4, -3],
    [-5, 3, -6, 5, -4],
    [-5, -3, -5, -3, -5, 3, 3, 3],
    [-5, -4, 7, 3, 6, 8, -4, 6],
    [9, -7, 6, -5, -5, 3, 7, -4, 9, -6, -6]]
  base := #[2, 3, 4, 8, 5]
  sizes := [6, 5, 4, 16, 3]
  k := 0
  pX := 2
  eX := 2
  pY := 3
  eY := 0
  pXY := 5
  eXY := 0

end CFSG.Quasithin.H.Code22.Native
