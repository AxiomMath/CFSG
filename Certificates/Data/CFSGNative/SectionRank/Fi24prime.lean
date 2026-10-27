module

public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CFSG.SectionRank.Native

@[expose] def fi24primeData : Data where
  seedA := include_str "../../../../CFSG/Blueprint/Data/F24G1-f3r781B0.m1"
  seedB := include_str "../../../../CFSG/Blueprint/Data/F24G1-f3r781B0.m2"
  nregs := 121
  prog := [
      .mul 1 1 2, .mul 0 1 3, .mul 3 3 4, .mul 4 0 5, .mul 5 2 6, .pow 11 6 7, .mul 0 1 8,
      .mul 8 0 9, .mul 9 1 10, .mul 10 0 11, .mul 11 2 12, .mul 12 0 13, .mul 13 1 14, .mul 9 2 15,
      .mul 15 0 16, .mul 16 2 17, .mul 17 0 18, .mul 18 1 19, .mul 18 2 20, .mul 16 1 21,
      .mul 21 0 22, .mul 22 1 23, .mul 11 1 24, .mul 24 0 25, .mul 25 2 26, .mul 1 0 27,
      .mul 27 2 28, .mul 28 0 29, .mul 29 2 30, .mul 30 0 31, .mul 31 2 32, .mul 32 0 33,
      .mul 2 0 34, .mul 34 2 35, .mul 35 0 36, .mul 36 2 37, .mul 37 0 38, .mul 38 1 39,
      .mul 39 0 40, .mul 34 1 41, .mul 41 0 42, .mul 42 1 43, .mul 43 0 44, .mul 44 2 45,
      .mul 45 0 46, .mul 31 1 47, .mul 47 0 48, .mul 44 1 49, .mul 49 0 50, .mul 36 1 51,
      .mul 51 0 52, .mul 52 2 53, .mul 53 0 54, .mul 42 2 55, .mul 55 0 56, .mul 56 2 57,
      .mul 57 0 58, .mul 14 19 59, .mul 59 20 60, .mul 60 23 61, .mul 61 19 62, .mul 62 20 63,
      .mul 63 26 64, .mul 64 33 65, .mul 65 40 66, .mul 66 46 67, .mul 67 48 68, .mul 68 50 69,
      .mul 69 54 70, .mul 70 58 71, .pow 3 71 72, .mul 22 2 73, .mul 0 2 74, .mul 74 0 75,
      .mul 75 1 76, .mul 76 0 77, .mul 77 2 78, .mul 78 0 79, .mul 79 2 80, .mul 79 1 81,
      .mul 38 2 82, .mul 82 0 83, .mul 29 1 84, .mul 84 0 85, .mul 85 2 86, .mul 86 0 87,
      .mul 56 1 88, .mul 88 0 89, .mul 85 1 90, .mul 90 0 91, .mul 73 23 92, .mul 92 23 93,
      .mul 93 80 94, .mul 94 20 95, .mul 95 73 96, .mul 96 81 97, .mul 97 58 98, .mul 98 83 99,
      .mul 99 48 100, .mul 100 87 101, .mul 101 89 102, .mul 102 91 103, .mul 103 58 104,
      .pow 6 104 105, .mul 13 2 106, .mul 25 1 107, .mul 59 80 108, .mul 108 106 109,
      .mul 109 81 110, .mul 110 80 111, .mul 111 107 112, .mul 112 48 113, .mul 113 46 114,
      .mul 114 58 115, .mul 115 54 116, .mul 116 54 117, .mul 117 48 118, .mul 118 46 119,
      .pow 4 119 120]
  outs := [7, 72, 105, 120]
  tests := [0]

end CFSG.SectionRank.Native
