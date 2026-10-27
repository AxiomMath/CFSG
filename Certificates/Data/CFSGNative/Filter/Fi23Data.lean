module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def fi23Sec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/F23G1-f3r253B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/F23G1-f3r253B0.m2"
  nregs := 8
  prog := [
      .mul 0 1 2, .pow 12 2 2, .mul 1 2 2, .mul 2 2 2, .pow 8 2 3, .mul 0 2 4, .mul 2 0 5,
      .mul 4 0 6, .mul 5 2 5, .mul 6 3 3, .mul 5 2 5, .mul 5 0 5, .mul 5 2 6, .mul 6 2 6,
      .mul 6 2 6, .mul 6 2 2, .pow 14 4 4, .pow 2 3 3, .pow 6 5 5, .pow 3 6 6, .pow 9 2 2]
  outs := [4, 3, 5, 6, 2]
  tReg := 7
  tests := [0]

end CFSG.SectionRank.Native
