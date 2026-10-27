module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def ruSec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/RuG1-f2r28B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/RuG1-f2r28B0.m2"
  nregs := 24
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 4 2 5, .mul 4 1 6, .mul 1 1 7, .mul 6 5 8,
      .mul 7 8 9, .pow 11 8 10, .mul 9 7 11, .mul 11 8 12, .mul 12 8 13, .pow 6 13 14,
      .mul 7 14 15, .mul 15 7 16, .mul 10 16 17, .mul 17 8 18, .mul 7 18 19, .mul 19 7 20,
      .mul 10 18 21, .mul 21 8 22]
  outs := [14, 16, 18, 20, 22]
  tReg := 23
  tests := [0]

end CFSG.SectionRank.Native
