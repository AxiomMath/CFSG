module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def fi24primeSec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/F24G1-f3r781B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/F24G1-f3r781B0.m2"
  nregs := 11
  prog := [
      .pow 2 1 2, .mul 2 0 3, .mul 3 1 4, .mul 0 4 5, .pow 3 5 5, .mul 5 2 5, .pow 18 5 5,
      .mul 1 0 6, .mul 6 2 7, .mul 6 1 6, .mul 3 2 3, .mul 3 0 3, .mul 7 0 7, .mul 4 0 4,
      .mul 6 0 6, .mul 6 1 8, .mul 3 2 3, .mul 3 0 3, .mul 6 2 6, .mul 7 2 9, .mul 7 1 7,
      .mul 4 2 4, .mul 4 0 4, .mul 6 0 6, .mul 6 9 9, .mul 0 9 9, .pow 3 9 9, .mul 7 0 7,
      .mul 8 0 8, .mul 8 2 8, .mul 4 2 4, .mul 4 0 4, .mul 7 1 7, .mul 8 0 8, .mul 3 1 3,
      .mul 3 0 3, .mul 7 0 7, .mul 8 1 8, .mul 4 2 4, .mul 4 0 4, .mul 4 8 8, .mul 0 8 8,
      .pow 3 8 8, .mul 7 1 7, .mul 3 2 2, .mul 7 0 7, .mul 7 2 2, .mul 0 2 2, .pow 3 2 2]
  outs := [0, 5, 9, 8, 2]
  tReg := 10
  tests := [0]

end CFSG.SectionRank.Native
