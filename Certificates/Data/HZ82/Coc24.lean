module

public import Certificates.Data.CFSGNative.Mathieu.Check

public section

namespace CFSG.Quasithin.H.Coc24.Native

open CFSG.Sporadic.Mathieu.Native CFSG.Sporadic.Th.Native

@[expose] def lzData : Data where
  tA := #[15, 14, 13, 12, 23, 21, 20, 22, 19, 16, 18, 17, 0, 1, 2, 3, 4, 6, 7, 5, 11, 8, 10, 9]
  tB := #[16, 17, 18, 19, 20, 21, 22, 23, 7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8]
  words :=
    #[[1],
    [2],
    [3, -4, 3, 3, -4, 4],
    [-4, -3, -3, -5, -4, 5],
    [6, 5, 6, 3, -3, 4, 3],
    [7, -6, 7, -3, 7, -5, -3],
    [6, -3, -4, 5, 8, 6],
    [-7, -5, -6, -3, -4, 8, -9, -7, 5, 5],
    [-7, -5, 6, 3, -5, 8, 7, -6, -3, -7, 3]]
  base := #[0, 4, 5, 8, 1]
  sizes := [24, 20, 3, 16, 3]
  k := 0
  pX := 2
  eX := 1
  pY := 3
  eY := 0
  pXY := 5
  eXY := 0

@[expose] def a6colData : Data where
  tA := #[3, 5, 4, 0, 1, 2]
  tB := #[4, 5, 1, 0, 3, 2]
  words :=
    #[[1],
    [2],
    [-3, -4],
    [5, 5, -4, -3, -4, -5, -4, -3],
    [6, -5, -5, -4, 3, 6, -4, 6, 3, -4]]
  base := #[0, 1, 2, 3]
  sizes := [6, 5, 4, 3]
  k := 0
  pX := 2
  eX := 1
  pY := 3
  eY := 0
  pXY := 5
  eXY := 0

end CFSG.Quasithin.H.Coc24.Native
