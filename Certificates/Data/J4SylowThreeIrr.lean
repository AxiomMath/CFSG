module

public import Certificates.Data.CFSGNative.SectionRank.J4Local

public section

namespace CFSG.SectionRank.Native

@[expose] def j4Sylow3IrrData : CubData where
  seedA := j4Sylow3Data.seedA
  seedB := j4Sylow3Data.seedB
  nregs := 89
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .pow 5 4 6, .mul 3 1 7, .pow 8 5 8, .pow 9 2 9,
      .pow 36 9 10, .mul 10 6 11, .mul 11 9 12, .pow 21 7 13, .pow 36 13 14, .mul 14 8 15,
      .mul 15 13 16, .pow 2 16 17, .mul 12 16 18, .mul 18 12 19, .mul 19 17 20, .mul 20 12 21,
      .mul 21 17 22, .mul 22 12 23, .mul 23 17 24, .mul 24 12 25, .mul 25 17 26, .mul 26 12 27,
      .mul 27 16 28, .mul 28 12 29, .mul 29 17 30, .mul 30 12 31, .mul 31 17 32, .mul 32 12 33,
      .mul 33 16 34, .mul 34 12 35, .mul 35 17 36, .pow 14 36 37, .pow 2 37 38, .mul 12 17 39,
      .mul 39 12 40, .mul 40 16 41, .mul 41 12 42, .mul 42 16 43, .mul 43 12 44, .mul 44 16 45,
      .mul 45 12 46, .mul 46 17 47, .mul 47 12 48, .mul 48 16 49, .mul 49 12 50, .mul 50 17 51,
      .mul 51 12 52, .mul 52 16 53, .pow 6 53 54, .pow 3 54 55, .mul 54 37 56, .mul 56 55 57,
      .mul 57 38 58, .mul 37 58 59, .mul 59 38 60, .pow 1 60 61, .mul 61 54 62, .mul 12 16 63,
      .mul 63 12 64, .mul 64 16 65, .mul 65 12 66, .mul 66 17 67, .mul 67 12 68, .mul 68 16 69,
      .mul 69 12 70, .mul 70 17 71, .mul 71 12 72, .mul 72 16 73, .mul 73 12 74, .mul 74 16 75,
      .pow 4 75 76, .pow 2 76 77, .mul 76 37 78, .mul 78 77 79, .mul 79 38 80, .mul 37 80 81,
      .mul 81 38 82, .pow 3 82 83, .mul 83 76 84, .pow 4 84 85, .pow 3 62 86, .mul 62 85 87,
      .mul 87 86 88]
  rx := 85
  ry := 88
  rh := 62
  r := 3
  oh := 4
  a := 0
  b := 1
  c := 2
  d := 0
  k := 0
  l := 2
  μ := 1
  t := 0

end CFSG.SectionRank.Native
