module

public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def mclData : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/McLG1-f3r21B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/McLG1-f3r21B0.m2"
  nregs := 37
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 7, .mul 1 7 8,
      .mul 4 4 9, .mul 4 9 10, .pow 13 10 11, .mul 11 8 12, .mul 12 10 13, .mul 3 3 14,
      .mul 3 14 15, .mul 14 15 16, .pow 11 16 17, .mul 17 0 18, .mul 18 16 19, .mul 19 13 20,
      .mul 20 13 21, .mul 21 13 22, .pow 4 22 23, .pow 7 13 24, .mul 19 24 25, .mul 25 24 26,
      .mul 26 24 27, .pow 4 27 28, .mul 13 19 29, .mul 29 13 30, .mul 30 13 31, .pow 4 31 32,
      .mul 13 13 33, .mul 33 19 34, .mul 34 13 35, .pow 4 35 36]
  outs := [23, 28, 32, 36]
  tests := [0]

end CFSG.SectionRank.Native
