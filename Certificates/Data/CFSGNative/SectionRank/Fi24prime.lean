module

public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def fi24primeData : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/F24G1-f3r781B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/F24G1-f3r781B0.m2"
  nregs := 121
  prog := [
      .mul 1 1 2, .mul 0 2 3, .mul 0 1 4, .mul 3 4 5, .mul 3 5 6, .mul 6 5 7, .mul 4 5 8,
      .mul 4 6 9, .mul 6 4 10, .mul 3 7 11, .mul 3 6 12, .mul 5 4 13, .mul 7 8 14, .mul 3 12 15,
      .mul 13 8 16, .mul 11 5 17, .mul 4 9 18, .mul 7 10 19, .mul 10 11 20, .mul 18 9 21,
      .mul 14 7 22, .mul 18 0 23, .mul 20 21 24, .mul 22 23 25, .mul 24 25 26, .mul 2 16 27,
      .mul 16 8 28, .mul 6 17 29, .mul 15 6 30, .mul 8 14 31, .mul 27 28 32, .mul 29 30 33,
      .mul 31 3 34, .mul 32 33 35, .mul 35 34 36, .mul 19 17 37, .mul 10 4 38, .mul 11 9 39,
      .mul 15 11 40, .mul 37 38 41, .mul 39 40 42, .mul 41 42 43, .mul 43 19 44, .pow 11 13 45,
      .pow 3 26 46, .pow 6 36 47, .pow 4 44 48]
  outs := [45, 46, 47, 48]
  tests := [0]

end CFSG.SectionRank.Native
