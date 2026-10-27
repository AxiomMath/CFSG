module

public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def onanData : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/ONG1-f3r154B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/ONG1-f3r154B0.m2"
  nregs := 38
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 7, .mul 6 7 8,
      .mul 8 8 9, .mul 8 8 10, .mul 5 3 11, .pow 19 11 12, .pow 30 12 13, .mul 13 10 14,
      .mul 14 12 15, .mul 3 5 16, .mul 4 3 17, .mul 17 2 18, .pow 12 18 19, .mul 16 19 20,
      .pow 14 20 21, .mul 21 9 22, .mul 22 20 23, .mul 15 23 24, .mul 24 23 25, .pow 4 25 26,
      .mul 15 15 27, .mul 27 23 28, .mul 28 23 29, .pow 2 29 30, .mul 15 23 31, .mul 31 23 32,
      .mul 32 15 33, .pow 2 33 34, .mul 23 15 35, .mul 35 23 36, .pow 4 36 37]
  outs := [26, 30, 34, 37]
  tests := [0]

end CFSG.SectionRank.Native
