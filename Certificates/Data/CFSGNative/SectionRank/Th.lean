module

public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def thData : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m2"
  nregs := 45
  prog := [
      .mul 0 1 2, .mul 2 1 3, .pow 4 2 4, .mul 4 1 5, .mul 5 3 6, .mul 3 3 7, .mul 7 7 8,
      .mul 4 7 9, .mul 8 9 10, .pow 3 8 11, .mul 11 4 12, .mul 10 11 13, .pow 18 13 14,
      .mul 14 0 15, .mul 15 13 16, .pow 19 12 17, .mul 17 6 18, .mul 18 12 19, .pow 4 19 20,
      .mul 16 19 21, .pow 10 21 22, .pow 11 19 23, .mul 23 16 24, .mul 24 23 25, .mul 25 23 26,
      .pow 1 16 27, .mul 26 27 28, .mul 28 19 29, .mul 29 19 30, .mul 30 19 31, .mul 31 19 32,
      .mul 32 27 33, .pow 2 33 34, .mul 23 27 35, .mul 35 23 36, .mul 36 23 37, .mul 37 16 38,
      .mul 38 23 39, .mul 39 23 40, .mul 40 16 41, .mul 41 19 42, .mul 42 19 43, .pow 2 43 44]
  outs := [20, 22, 34, 44]
  tests := [0]

end CFSG.SectionRank.Native
