module

public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def co3Data : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m2"
  nregs := 29
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .pow 5 5 6, .pow 4 2 7, .pow 4 4 8,
      .mul 7 8 9, .pow 13 9 10, .mul 10 1 11, .mul 11 9 12, .pow 2 6 13, .mul 13 12 14,
      .pow 8 14 15, .pow 3 12 16, .mul 6 16 17, .pow 8 17 18, .mul 13 12 19, .mul 19 6 20,
      .mul 20 12 21, .mul 21 12 22, .pow 4 22 23, .mul 13 16 24, .mul 24 6 25, .mul 25 12 26,
      .mul 26 12 27, .pow 4 27 28]
  outs := [15, 18, 23, 28]
  tests := [0]

end CFSG.SectionRank.Native
