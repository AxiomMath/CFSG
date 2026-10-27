module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def hsSec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/HSG1-f2r20B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/HSG1-f2r20B0.m2"
  nregs := 29
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 6 7, .mul 6 7 8,
      .mul 7 8 9, .mul 0 9 10, .mul 10 10 11, .mul 10 11 12, .mul 12 6 13, .mul 12 13 14,
      .pow 4 13 15, .mul 13 12 16, .mul 14 12 17, .pow 4 17 18, .mul 16 13 19, .mul 19 13 20,
      .pow 5 20 21, .pow 10 20 22, .mul 20 12 23, .mul 20 13 24, .pow 2 24 25, .mul 23 13 26,
      .mul 26 12 27, .pow 4 27 28]
  outs := [15, 18, 21, 25, 28]
  tReg := 22
  tests := [0]

end CFSG.SectionRank.Native
