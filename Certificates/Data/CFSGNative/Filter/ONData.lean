module

public import Certificates.Data.CFSGNative.Filter.Sec2
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def onanSec : SecData where
  seedA := include_str "../../../../CFSG/Blueprint/Data/ONG1-f3r154B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/ONG1-f3r154B0.m2"
  nregs := 9
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 3, .pow 10 3 2, .mul 2 1 4, .mul 1 2 5, .pow 19 5 5,
      .mul 5 4 4, .pow 14 4 4, .pow 5 3 5, .mul 4 3 6, .mul 3 3 7, .mul 6 4 8, .mul 6 3 6,
      .mul 7 4 7, .mul 8 3 8, .mul 6 4 6, .mul 7 3 7, .mul 8 3 8, .mul 6 3 6, .mul 7 3 7,
      .mul 8 4 8, .mul 6 3 6, .mul 8 3 8, .mul 6 4 4, .mul 8 3 8, .mul 4 3 3, .pow 4 7 7,
      .pow 4 4 4, .pow 2 8 8, .pow 2 3 3]
  outs := [5, 7, 4, 8, 3]
  tReg := 2
  tests := [0]

end CFSG.SectionRank.Native
