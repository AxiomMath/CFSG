module

public import CFSG.RankThree.PartTwo.Census.Sporadic.RankFourCert
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.SectionRank.Native

@[expose] def co2W3 : W4Data where
  base :=
    { seedA := include_str "../../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m1"
      seedB := include_str "../../../CFSG/Blueprint/Data/Co2G1-f2r22B0.m2"
      nregs := 81
      prog := [
          .pow 4 1 2, .mul 2 0 3, .mul 2 3 4, .mul 4 3 5, .mul 5 3 6, .mul 3 6 7, .mul 4 7 8,
          .mul 8 5 9, .pow 5 9 10, .mul 8 3 11, .pow 24 11 12, .pow 17 6 13, .mul 12 13 14,
          .pow 3 5 15, .pow 7 14 16, .mul 15 16 17, .mul 14 17 18, .mul 10 18 19, .mul 19 18 20,
          .mul 20 18 21, .mul 0 1 22, .mul 22 1 23, .mul 22 23 24, .mul 22 24 25, .mul 25 22 26,
          .mul 26 23 27, .mul 24 27 28, .pow 5 28 29, .mul 21 29 30, .mul 30 18 31, .pow 9 31 32,
          .mul 18 10 33, .mul 33 18 34, .pow 17 25 35, .mul 22 27 36, .pow 24 36 37, .mul 35 37 38,
          .pow 7 38 39, .pow 3 24 40, .mul 39 40 41, .mul 41 38 42, .mul 34 42 43, .mul 43 29 44,
          .mul 44 29 45, .mul 45 42 46, .mul 46 10 47, .mul 47 29 48, .mul 48 10 49, .mul 29 42 50,
          .mul 42 50 51, .mul 18 51 52, .mul 10 52 53, .mul 10 53 54, .mul 18 54 55, .mul 29 55 56,
          .mul 10 56 57, .mul 29 57 58, .mul 58 32 59, .mul 59 49 60, .mul 32 60 61, .mul 49 61 62,
          .pow 6 62 63, .mul 10 18 64, .mul 29 64 65, .mul 65 32 66, .mul 42 29 67, .mul 67 10 68,
          .mul 66 68 69, .mul 32 69 70, .pow 2 70 71, .mul 71 62 72, .pow 2 72 73, .mul 29 42 74,
          .mul 74 32 75, .mul 18 10 76, .mul 75 76 77, .mul 32 77 78, .pow 2 78 79, .mul 71 79 80]
      outs := [63, 73, 80]
      tests := [0] }
  inv := 32

end CFSG.RankThree.PartTwo.Census
