module

public import Certificates.Data.CFSGNative.SectionRank.F2Fast

public section

namespace CFSG.SectionRank.Native

@[expose] def bData : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/BG1-f2r4370B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/BG1-f2r4370B0.m2"
  nregs := 69
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 5 6, .mul 6 6 7, .mul 6 7 8,
      .mul 7 8 9, .mul 3 3 10, .mul 10 10 11, .mul 11 11 12, .mul 12 12 13, .mul 3 13 14,
      .pow 54 14 15, .mul 15 1 16, .mul 16 14 17, .mul 2 2 18, .mul 2 18 19, .mul 19 19 20,
      .mul 20 20 21, .mul 2 21 22, .pow 54 22 23, .mul 23 9 24, .mul 24 22 25, .mul 25 17 26,
      .mul 26 17 27, .pow 4 26 28, .mul 28 17 29, .mul 29 27 30, .mul 27 27 31, .mul 31 31 32,
      .mul 28 31 33, .mul 32 33 34, .pow 3 32 35, .mul 35 28 36, .mul 34 35 37, .pow 18 37 38,
      .mul 38 25 39, .mul 39 37 40, .pow 19 36 41, .mul 41 30 42, .mul 42 36 43, .pow 4 43 44,
      .mul 40 43 45, .pow 10 45 46, .pow 11 43 47, .mul 47 40 48, .mul 48 47 49, .mul 49 47 50,
      .pow 1 40 51, .mul 50 51 52, .mul 52 43 53, .mul 53 43 54, .mul 54 43 55, .mul 55 43 56,
      .mul 56 51 57, .pow 2 57 58, .mul 47 51 59, .mul 59 47 60, .mul 60 47 61, .mul 61 40 62,
      .mul 62 47 63, .mul 63 47 64, .mul 64 40 65, .mul 65 43 66, .mul 66 43 67, .pow 2 67 68]
  outs := [44, 46, 58, 68]
  tests := [0]

end CFSG.SectionRank.Native
