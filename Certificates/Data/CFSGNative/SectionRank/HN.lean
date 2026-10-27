module

public import Certificates.Data.CFSGNative.SectionRank.Fp

public section

namespace CFSG.SectionRank.Native

@[expose] def hnData : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/HNG1-f5r133B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/HNG1-f5r133B0.m2"
  nregs := 61
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 4 6, .mul 2 6 7, .mul 7 3 8,
      .mul 8 8 9, .mul 8 9 10, .mul 9 10 11, .pow 3 11 12, .mul 0 12 13, .mul 13 0 14,
      .mul 14 12 15, .mul 15 0 16, .mul 16 12 17, .mul 17 12 18, .pow 1 0 19, .mul 18 19 20,
      .mul 20 12 21, .mul 21 19 22, .mul 22 11 23, .mul 23 19 24, .mul 12 0 25, .mul 25 11 26,
      .mul 26 19 27, .mul 27 12 28, .mul 28 19 29, .mul 29 12 30, .mul 30 0 31, .mul 31 11 32,
      .mul 32 0 33, .mul 33 11 34, .mul 34 0 35, .pow 2 35 36, .mul 0 11 37, .mul 37 11 38,
      .mul 38 0 39, .mul 39 11 40, .mul 40 19 41, .mul 41 11 42, .mul 42 19 43, .mul 43 11 44,
      .mul 44 11 45, .mul 45 0 46, .mul 46 11 47, .pow 7 47 48, .mul 12 19 49, .mul 49 11 50,
      .mul 50 19 51, .mul 51 12 52, .mul 52 12 53, .mul 53 19 54, .mul 54 11 55, .mul 55 0 56,
      .mul 56 11 57, .mul 57 19 58, .mul 58 12 59, .pow 7 59 60]
  outs := [24, 36, 48, 60]
  tests := [0]

end CFSG.SectionRank.Native
