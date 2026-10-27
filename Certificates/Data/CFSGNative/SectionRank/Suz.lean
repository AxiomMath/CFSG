module

public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def suzData : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/SuzG1-f3r64B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/SuzG1-f3r64B0.m2"
  nregs := 41
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 4 4 5, .mul 2 5 6, .mul 6 6 7, .mul 7 7 8,
      .mul 7 8 9, .pow 5 3 10, .pow 12 10 11, .mul 11 9 12, .mul 12 10 13, .pow 6 2 14,
      .pow 12 14 15, .mul 15 8 16, .mul 16 14 17, .mul 17 13 18, .mul 18 17 19, .mul 19 13 20,
      .mul 20 17 21, .pow 3 13 22, .mul 21 22 23, .pow 4 23 24, .mul 17 13 25, .mul 25 17 26,
      .mul 26 13 27, .mul 27 13 28, .pow 6 28 29, .mul 17 13 30, .mul 30 17 31, .mul 31 22 32,
      .mul 32 17 33, .mul 33 13 34, .pow 4 34 35, .mul 17 13 36, .mul 36 13 37, .mul 37 17 38,
      .mul 38 13 39, .pow 6 39 40]
  outs := [24, 29, 35, 40]
  tests := [0]

end CFSG.SectionRank.Native
