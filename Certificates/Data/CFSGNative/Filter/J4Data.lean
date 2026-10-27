module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def j4Sec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/J4G1-f2r112B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/J4G1-f2r112B0.m2"
  nregs := 28
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 5 6, .mul 6 6 7, .mul 7 7 8,
      .mul 3 1 9, .pow 36 9 10, .mul 10 8 11, .mul 11 9 12, .pow 36 2 13, .mul 13 0 14,
      .mul 14 2 15, .mul 15 12 16, .pow 2 12 17, .pow 14 16 18, .mul 15 18 19, .mul 19 15 20,
      .mul 17 18 21, .mul 21 12 22, .mul 15 22 23, .mul 23 15 24, .mul 17 24 25, .mul 25 12 26]
  outs := [18, 20, 22, 24, 26]
  tReg := 27
  tests := [0]

end CFSG.SectionRank.Native
