module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def suzSec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/SuzG1-f3r64B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/SuzG1-f3r64B0.m2"
  nregs := 11
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 4 4 5, .mul 4 5 5, .mul 3 3 3, .mul 3 3 4,
      .mul 3 4 4, .pow 12 4 3, .mul 3 5 5, .mul 5 4 4, .pow 12 2 5, .mul 5 0 5, .mul 5 2 2,
      .pow 4 4 5, .mul 2 4 3, .mul 4 2 6, .mul 3 2 7, .mul 6 5 6, .mul 7 5 7, .mul 6 5 8,
      .mul 8 2 8, .mul 8 4 8, .mul 8 2 9, .mul 9 5 5, .mul 5 2 2, .mul 2 4 4, .pow 9 3 3,
      .pow 4 7 7, .pow 6 8 8, .pow 2 4 4]
  outs := [6, 3, 7, 8, 4]
  tReg := 10
  tests := [0]

end CFSG.SectionRank.Native
