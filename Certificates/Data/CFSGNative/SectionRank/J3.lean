module

public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def j3Data : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/J3G1-f2r80B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/J3G1-f2r80B0.m2"
  nregs := 30
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 4 4 5, .mul 2 5 6, .mul 3 3 7, .mul 3 7 8,
      .mul 8 8 9, .pow 18 9 10, .mul 10 6 11, .mul 11 9 12, .mul 2 2 13, .mul 13 13 14,
      .mul 14 14 15, .mul 2 15 16, .pow 18 16 17, .mul 17 0 18, .mul 18 16 19, .mul 19 12 20,
      .mul 20 12 21, .pow 4 21 22, .pow 7 12 23, .mul 19 23 24, .mul 24 23 25, .pow 4 25 26,
      .mul 12 19 27, .mul 27 12 28, .pow 4 28 29]
  outs := [22, 26, 29]
  tests := [0]

end CFSG.SectionRank.Native
