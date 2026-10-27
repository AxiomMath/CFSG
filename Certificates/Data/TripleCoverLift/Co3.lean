module

public import Certificates.Data.TripleCoverLift.Check

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.SectionRank.Native

@[expose] def co3LiftProg0 : List Op := [
    .mul 0 1 2, .pow 4 2 3, .mul 2 1 4, .mul 2 4 5, .pow 4 5 6, .mul 3 6 7, .pow 13 7 8,
    .mul 8 1 9, .mul 9 7 10, .mul 10 10 11, .mul 2 5 12, .pow 5 12 13, .pow 2 13 14, .mul 14 10 15,
    .pow 8 15 16, .pow 3 1 17, .pow 2 0 18, .mul 17 18 19, .mul 17 19 20, .mul 20 19 21,
    .pow 4 21 22, .pow 4 19 23, .mul 22 23 24, .pow 13 24 25, .mul 17 25 26, .mul 24 26 27,
    .mul 27 16 28, .mul 28 10 29, .mul 16 29 30, .mul 27 29 31, .mul 31 10 32, .mul 30 32 33,
    .mul 21 19 34, .pow 5 34 35, .mul 35 32 36, .mul 36 13 37, .pow 2 37 38, .mul 33 38 39,
    .pow 2 16 40, .mul 35 16 41, .mul 41 13 42, .mul 40 42 43, .mul 43 29 44, .mul 44 32 45,
    .mul 45 37 46, .pow 2 42 47, .mul 16 47 48, .mul 48 29 49, .pow 2 32 50, .mul 49 50 51,
    .mul 13 10 52, .mul 52 13 53, .mul 53 10 54, .mul 54 13 55, .mul 55 13 56, .mul 56 10 57,
    .mul 57 13 58, .mul 58 13 59, .mul 59 10 60, .mul 60 13 61, .mul 61 10 62, .mul 62 13 63,
    .mul 63 10 64, .mul 64 13 65, .mul 13 13 66, .mul 66 10 67, .mul 67 13 68, .mul 68 10 69,
    .mul 69 10 70, .mul 70 13 71, .mul 71 13 72, .mul 72 10 73, .mul 73 10 74, .mul 74 13 75]

@[expose] def co3Lift : LiftData where
  base :=
    { seedA := include_str "../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m1"
      seedB := include_str "../../../CFSG/Blueprint/Data/Co3G1-f2r22B0.m2"
      nregs := 76
      prog := co3LiftProg0
      outs := [39, 46, 51]
      tests := [0, 1] }
  inv₁ := 11
  inv₂ := 11
  units := [(65, 8), (75, 12), (10, 4)]
  rels := [
    .inv 65 0, .fix 75 0, .inv 75 1, .fix 10 0, .fix 10 1, .inv 10 2]

end CFSG.RankThree.PartTwo.Sec4.Census
