module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.Fp

public section

namespace CFSG.SectionRank.Native

@[expose] def heSec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/HeG1-f7r50B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/HeG1-f7r50B0.m2"
  nregs := 8
  prog := [
      .mul 0 1 2, .mul 2 1 2, .mul 2 1 3, .mul 3 1 3, .mul 3 1 4, .mul 4 1 5, .mul 4 2 2,
      .mul 3 5 5, .mul 2 5 5, .mul 0 5 2, .mul 2 5 3, .mul 3 5 3, .mul 3 5 3, .mul 3 0 4,
      .mul 3 5 3, .mul 4 5 4, .mul 4 0 6, .pow 5 5 5, .pow 6 2 2, .pow 2 3 3, .pow 3 4 4,
      .pow 2 6 6]
  outs := [5, 2, 3, 6, 4]
  tReg := 7
  tests := [0]

end CFSG.SectionRank.Native
