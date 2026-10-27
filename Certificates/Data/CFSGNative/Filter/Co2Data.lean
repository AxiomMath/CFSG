module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def co2Sec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m2"
  nregs := 35
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 7, .mul 4 4 8,
      .mul 8 8 9, .mul 2 2 10, .mul 10 10 11, .mul 10 2 12, .mul 11 12 13, .mul 6 6 14,
      .mul 14 14 15, .mul 7 7 16, .mul 16 16 17, .mul 16 17 18, .mul 15 18 19, .pow 7 19 20,
      .mul 20 13 21, .mul 21 19 22, .pow 5 9 23, .pow 3 22 24, .pow 2 22 25, .mul 23 25 26,
      .mul 26 9 27, .mul 23 27 28, .mul 28 9 29, .mul 24 27 30, .mul 30 22 31, .mul 23 29 32,
      .mul 32 9 33]
  outs := [25, 27, 29, 31, 33]
  tReg := 34
  tests := [0, 1]

end CFSG.SectionRank.Native
