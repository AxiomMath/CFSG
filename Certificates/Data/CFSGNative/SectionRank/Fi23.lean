module

public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def fi23Data : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/F23G1-f3r253B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/F23G1-f3r253B0.m2"
  nregs := 41
  prog := [
      .mul 0 1 2, .mul 2 1 3, .pow 9 2 4, .pow 12 3 5, .mul 4 5 6, .mul 6 4 7, .pow 17 7 8,
      .mul 0 8 9, .mul 9 8 10, .mul 10 8 11, .pow 20 11 12, .mul 7 7 13, .mul 13 0 14, .mul 14 7 15,
      .pow 20 15 16, .mul 8 8 17, .mul 17 0 18, .mul 18 8 19, .mul 19 8 20, .pow 1 0 21,
      .mul 20 21 22, .mul 22 7 23, .mul 23 21 24, .mul 24 7 25, .mul 25 0 26, .mul 26 7 27,
      .mul 27 7 28, .mul 8 8 29, .mul 29 0 30, .mul 30 8 31, .mul 31 0 32, .mul 32 8 33,
      .mul 33 8 34, .mul 34 21 35, .mul 35 8 36, .mul 36 8 37, .mul 37 8 38, .mul 38 8 39,
      .pow 4 39 40]
  outs := [12, 16, 28, 40]
  tests := [0]

end CFSG.SectionRank.Native
