module

public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

@[expose] def co2Data : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m2"
  nregs := 38
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 7, .mul 2 7 8,
      .mul 4 7 9, .pow 5 9 10, .pow 3 4 11, .pow 17 5 12, .pow 24 8 13, .mul 12 13 14, .pow 7 14 15,
      .mul 15 11 16, .mul 16 14 17, .mul 10 17 18, .pow 10 18 19, .mul 10 17 20, .mul 20 10 21,
      .mul 21 17 22, .mul 22 10 23, .pow 4 23 24, .mul 17 10 25, .mul 25 17 26, .mul 26 10 27,
      .mul 27 17 28, .pow 4 28 29, .pow 7 17 30, .mul 30 10 31, .mul 31 30 32, .mul 32 10 33,
      .mul 33 17 34, .mul 34 17 35, .mul 35 17 36, .pow 8 36 37]
  outs := [19, 24, 29, 37]
  tests := [0]

end CFSG.SectionRank.Native
