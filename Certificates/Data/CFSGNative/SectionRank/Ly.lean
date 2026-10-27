module

public import Certificates.Data.CFSGNative.SectionRank.Fp

public section

namespace CFSG.SectionRank.Native

@[expose] def lyData : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/LyG1-f5r111B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/LyG1-f5r111B0.m2"
  nregs := 38
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 7, .pow 3 7 8,
      .mul 4 6 9, .pow 31 9 10, .pow 66 10 11, .mul 11 0 12, .mul 12 10 13, .mul 3 5 14,
      .pow 13 14 15, .pow 66 15 16, .mul 15 8 17, .mul 17 16 18, .mul 13 18 19, .mul 19 13 20,
      .pow 3 18 21, .mul 20 21 22, .pow 6 22 23, .mul 13 21 24, .mul 24 13 25, .mul 25 18 26,
      .pow 6 26 27, .mul 13 18 28, .mul 28 13 29, .mul 29 18 30, .mul 30 18 31, .pow 6 31 32,
      .mul 18 13 33, .mul 33 18 34, .mul 34 13 35, .mul 35 18 36, .pow 6 36 37]
  outs := [23, 27, 32, 37]
  tests := [0]

end CFSG.SectionRank.Native
