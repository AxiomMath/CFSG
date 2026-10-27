module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def co3Sec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m2"
  nregs := 51
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 1 1 5, .pow 6 4 6, .pow 5 2 7, .pow 3 4 8,
      .mul 7 8 9, .pow 14 9 10, .mul 10 6 11, .mul 11 9 12, .pow 6 12 13, .mul 5 5 14,
      .mul 12 5 15, .mul 15 12 16, .mul 14 13 17, .mul 17 13 18, .mul 18 13 19, .mul 19 5 20,
      .pow 5 20 21, .mul 16 12 22, .pow 2 22 23, .mul 21 23 24, .mul 24 23 25, .mul 24 25 26,
      .mul 24 26 27, .mul 27 24 28, .mul 28 28 29, .mul 28 29 30, .mul 29 30 31, .mul 21 31 32,
      .mul 32 32 33, .mul 32 33 34, .mul 34 28 35, .mul 34 35 36, .pow 4 35 37, .mul 35 34 38,
      .mul 36 34 39, .pow 4 39 40, .mul 38 35 41, .mul 41 35 42, .pow 5 42 43, .pow 10 42 44,
      .mul 42 34 45, .mul 42 35 46, .pow 2 46 47, .mul 45 35 48, .mul 48 34 49, .pow 4 49 50]
  outs := [37, 40, 43, 47, 50]
  tReg := 44
  tests := [0, 1]

end CFSG.SectionRank.Native
