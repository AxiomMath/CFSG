module

public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def co1Data : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co1G1-f2r24B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co1G1-f2r24B0.m2"
  nregs := 56
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 7, .mul 2 7 8,
      .pow 22 3 9, .pow 20 2 10, .mul 9 10 11, .pow 18 3 12, .mul 11 12 13, .pow 14 7 14,
      .mul 14 14 15, .mul 6 8 16, .pow 6 16 17, .mul 15 17 18, .mul 18 14 19, .mul 13 19 20,
      .mul 20 19 21, .mul 20 21 22, .mul 20 22 23, .mul 23 20 24, .mul 24 21 25, .mul 20 25 26,
      .mul 22 25 27, .pow 5 27 28, .pow 3 22 29, .pow 17 23 30, .pow 24 26 31, .mul 30 31 32,
      .pow 7 32 33, .mul 33 29 34, .mul 34 32 35, .mul 28 35 36, .pow 10 36 37, .mul 28 35 38,
      .mul 38 28 39, .mul 39 35 40, .mul 40 28 41, .pow 4 41 42, .mul 35 28 43, .mul 43 35 44,
      .mul 44 28 45, .mul 45 35 46, .pow 4 46 47, .pow 7 35 48, .mul 48 28 49, .mul 49 48 50,
      .mul 50 28 51, .mul 51 35 52, .mul 52 35 53, .mul 53 35 54, .pow 8 54 55]
  outs := [37, 42, 47, 55]
  tests := [0]

end CFSG.SectionRank.Native
