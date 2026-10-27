module

public import CFSG.RankThree.PartTwo.Census.Sporadic.RankFourCert
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.SectionRank.Native

@[expose] def co3W3 : W4Data where
  base :=
    { seedA := include_str "../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m1"
      seedB := include_str "../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m2"
      nregs := 50
      prog := [
          .mul 0 1 2, .pow 4 2 3, .mul 2 1 4, .mul 2 4 5, .pow 4 5 6, .mul 3 6 7, .pow 13 7 8,
          .mul 8 1 9, .mul 9 7 10, .pow 3 1 11, .pow 2 0 12, .mul 11 12 13, .mul 11 13 14,
          .mul 14 13 15, .mul 15 13 16, .pow 5 16 17, .mul 10 17 18, .mul 18 17 19, .mul 2 5 20,
          .pow 5 20 21, .mul 19 21 22, .pow 4 15 23, .pow 4 13 24, .mul 23 24 25, .pow 13 25 26,
          .mul 11 26 27, .mul 25 27 28, .mul 22 28 29, .mul 29 21 30, .mul 30 10 31, .mul 31 28 32,
          .mul 32 17 33, .mul 33 28 34, .mul 34 21 35, .mul 35 28 36, .mul 36 21 37, .pow 2 37 38,
          .pow 2 21 39, .mul 39 10 40, .pow 8 40 41, .mul 17 41 42, .mul 42 21 43, .mul 28 41 44,
          .mul 44 10 45, .mul 28 45 46, .mul 46 10 47, .pow 2 47 48, .mul 45 48 49]
      outs := [43, 41, 49]
      tests := [0] }
  inv := 38

end CFSG.RankThree.PartTwo.Census
