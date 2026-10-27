module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def thSec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m2"
  nregs := 32
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 3 2 4, .mul 4 4 5, .pow 15 2 6, .pow 9 3 7, .mul 6 7 8,
      .pow 12 2 9, .mul 8 9 10, .pow 16 3 11, .mul 10 11 12, .pow 17 2 13, .mul 12 13 14,
      .pow 11 14 15, .mul 15 5 16, .mul 16 14 17, .mul 0 17 18, .pow 4 17 19, .mul 18 0 20,
      .mul 20 19 21, .pow 4 21 22, .mul 19 22 23, .mul 23 17 24, .mul 19 24 25, .mul 25 17 26,
      .mul 19 26 27, .mul 27 17 28, .mul 19 28 29, .mul 29 17 30]
  outs := [22, 24, 26, 28, 30]
  tReg := 31
  tests := [0]

end CFSG.SectionRank.Native
