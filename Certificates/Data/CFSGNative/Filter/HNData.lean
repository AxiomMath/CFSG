module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.Fp

public section

namespace CFSG.SectionRank.Native

@[expose] def hnSec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/HNG1-f5r133B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/HNG1-f5r133B0.m2"
  nregs := 9
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .pow 21 2 5, .mul 5 0 5, .mul 5 2 2, .pow 5 3 3,
      .pow 21 3 5, .mul 5 4 4, .mul 4 3 3, .pow 4 3 4, .mul 2 3 5, .mul 3 2 6, .mul 5 2 7,
      .mul 5 3 5, .mul 6 3 3, .mul 6 4 6, .mul 7 4 7, .mul 3 2 2, .mul 7 4 3, .mul 2 4 2,
      .mul 2 4 4, .pow 6 5 5, .pow 3 7 7, .pow 6 3 3, .pow 3 4 4]
  outs := [6, 5, 7, 3, 4]
  tReg := 8
  tests := [0]

end CFSG.SectionRank.Native
