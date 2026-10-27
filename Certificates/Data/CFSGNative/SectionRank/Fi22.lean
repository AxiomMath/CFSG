module

public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def fi22Data : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/F22G1-f3r77B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/F22G1-f3r77B0.m2"
  nregs := 41
  prog := [
      .mul 0 1 2, .mul 0 2 3, .mul 1 0 4, .pow 12 1 5, .mul 4 5 6, .mul 6 2 7, .mul 7 7 8,
      .mul 8 8 9, .mul 0 8 10, .mul 10 9 11, .mul 2 1 12, .mul 12 1 13, .mul 13 1 14, .mul 14 1 15,
      .mul 15 1 16, .mul 16 1 17, .mul 17 1 18, .mul 15 18 19, .pow 2 19 20, .mul 20 11 21,
      .mul 21 19 22, .pow 7 3 23, .mul 16 2 24, .mul 12 18 25, .mul 23 24 26, .mul 26 25 27,
      .mul 11 22 28, .mul 11 27 29, .mul 29 22 30, .mul 30 27 31, .pow 2 31 32, .pow 11 27 33,
      .mul 11 33 34, .mul 34 22 35, .mul 35 33 36, .pow 2 36 37, .mul 27 22 38, .mul 38 27 39,
      .pow 4 39 40]
  outs := [28, 32, 37, 40]
  tests := [0]

end CFSG.SectionRank.Native
