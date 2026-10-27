module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def co1Sec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co1G1-f2r24B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co1G1-f2r24B0.m2"
  nregs := 39
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 5 6 7, .mul 7 7 8,
      .mul 8 8 9, .mul 4 4 10, .mul 4 10 11, .mul 3 3 12, .mul 3 12 13, .mul 12 13 14,
      .pow 7 14 15, .mul 15 9 16, .mul 16 14 17, .mul 2 2 18, .mul 2 18 19, .mul 19 19 20,
      .pow 19 20 21, .mul 21 11 22, .mul 22 20 23, .mul 23 17 24, .pow 5 17 25, .mul 24 23 26,
      .mul 26 17 27, .mul 27 17 28, .pow 4 28 29, .mul 23 29 30, .mul 30 23 31, .mul 25 29 32,
      .mul 32 17 33, .mul 25 31 34, .mul 34 17 35, .mul 23 33 36, .mul 36 23 37]
  outs := [29, 31, 33, 35, 37]
  tReg := 38
  tests := [0]

end CFSG.SectionRank.Native
