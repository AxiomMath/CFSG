module

public import CFSG.RankThree.PartTwo.Census.Sporadic.RankFourCert
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.SectionRank.Native

@[expose] def thW3 : W4Data where
  base :=
    { seedA := include_str "../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m1"
      seedB := include_str "../../../CFSG/Blueprint/Data/ThG1-f2r248B0.m2"
      nregs := 78
      prog := [
          .pow 2 1 2, .mul 2 0 3, .mul 2 3 4, .mul 4 4 5, .mul 5 5 6, .pow 3 6 7, .pow 4 3 8,
          .mul 5 8 9, .mul 9 6 10, .mul 7 10 11, .pow 18 11 12, .mul 0 12 13, .mul 11 13 14,
          .mul 14 14 15, .mul 15 14 16, .mul 8 7 17, .mul 2 8 18, .mul 4 18 19, .pow 19 17 20,
          .mul 19 20 21, .mul 17 21 22, .mul 16 22 23, .mul 23 14 24, .mul 24 14 25, .mul 25 14 26,
          .mul 26 14 27, .mul 27 14 28, .pow 6 28 29, .mul 0 1 30, .mul 30 1 31, .mul 31 31 32,
          .mul 32 32 33, .pow 3 33 34, .pow 4 30 35, .mul 34 35 36, .pow 19 36 37, .mul 35 1 38,
          .mul 38 31 39, .mul 37 39 40, .mul 40 36 41, .mul 14 41 42, .mul 42 22 43, .mul 43 14 44,
          .mul 44 14 45, .mul 45 41 46, .mul 46 41 47, .mul 47 41 48, .mul 35 32 49, .mul 33 49 50,
          .mul 50 34 51, .pow 18 51 52, .mul 52 0 53, .mul 53 51 54, .mul 22 54 55, .mul 41 55 56,
          .mul 54 56 57, .mul 54 57 58, .mul 22 58 59, .mul 22 59 60, .mul 22 60 61, .mul 61 29 62,
          .mul 62 48 63, .mul 29 63 64, .mul 48 64 65, .pow 8 65 66, .mul 14 54 67, .mul 67 41 68,
          .mul 68 41 69, .mul 69 22 70, .mul 70 41 71, .mul 71 41 72, .mul 72 41 73, .mul 73 54 74,
          .mul 74 22 75, .mul 65 75 76, .mul 75 65 77]
      outs := [66, 76, 77]
      tests := [0] }
  inv := 29

end CFSG.RankThree.PartTwo.Census
