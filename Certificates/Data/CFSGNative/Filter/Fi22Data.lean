module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def fi22Sec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/F22G1-f3r77B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/F22G1-f3r77B0.m2"
  nregs := 8
  prog := [
      .mul 1 1 2, .mul 2 2 3, .mul 1 0 4, .mul 2 4 2, .mul 4 2 2, .mul 1 3 4, .mul 0 3 5,
      .mul 3 0 3, .pow 10 3 3, .mul 3 5 5, .mul 2 4 4, .mul 4 4 2, .mul 2 4 3, .mul 2 5 2,
      .mul 3 4 6, .mul 3 5 3, .mul 6 4 6, .mul 6 4 6, .mul 6 5 6, .mul 6 4 4, .mul 4 5 6,
      .pow 9 2 2, .pow 10 3 3, .pow 4 4 4, .pow 4 6 6]
  outs := [5, 2, 3, 4, 6]
  tReg := 7
  tests := [0]

end CFSG.SectionRank.Native
