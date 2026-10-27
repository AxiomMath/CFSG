module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBSignedCheck
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.SectionRank.QTK.CoverB

open CFSG.SectionRank.Native

@[expose] def onSignedProg : List Op := [
    .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 7, .mul 6 7 8, .mul 8 8 9,
    .mul 8 8 10, .mul 5 3 11, .pow 19 11 12, .pow 30 12 13, .mul 13 10 14, .mul 14 12 15,
    .mul 3 5 16, .pow 17 16 17, .mul 4 3 18, .mul 18 2 19, .pow 8 19 20, .mul 17 20 21,
    .pow 19 21 22, .mul 22 9 23, .mul 23 21 24, .pow 3 15 25, .pow 3 24 26, .mul 15 24 27,
    .mul 27 15 28, .mul 28 15 29, .mul 29 26 30, .mul 30 15 31, .mul 31 24 32, .mul 32 15 33,
    .mul 33 24 34, .mul 34 15 35, .mul 35 24 36, .mul 36 24 37, .mul 24 25 38, .mul 38 24 39,
    .mul 39 15 40, .mul 40 26 41, .mul 41 25 42, .mul 42 24 43, .mul 43 15 44, .mul 44 24 45,
    .mul 45 24 46, .mul 24 15 47, .mul 47 24 48, .mul 48 15 49, .mul 49 15 50, .mul 50 24 51,
    .mul 51 24 52, .mul 52 25 53, .mul 24 15 54, .mul 54 24 55, .mul 55 24 56, .mul 56 15 57,
    .mul 57 15 58, .mul 58 24 59, .mul 59 24 60, .mul 60 25 61, .mul 61 24 62, .mul 15 26 63,
    .mul 63 15 64, .mul 64 24 65, .mul 65 25 66, .mul 66 26 67, .mul 67 15 68, .mul 68 24 69,
    .mul 69 15 70, .mul 70 15 71, .mul 26 25 72, .mul 72 24 73, .mul 73 25 74, .mul 74 24 75,
    .mul 75 15 76, .mul 76 26 77, .mul 77 25 78, .mul 78 24 79, .mul 79 25 80, .mul 80 24 81,
    .mul 81 15 82]

@[expose] def onSigned : SignedData where
  base :=
    { seedA := include_str "../../CFSG/Blueprint/Data/ONG1-f3r154B0.m1"
      seedB := include_str "../../CFSG/Blueprint/Data/ONG1-f3r154B0.m2"
      nregs := 83
      prog := onSignedProg
      outs := []
      tests := [0] }
  t₁ := 37
  t₂ := 46
  a := 53
  b := 62
  d₁ := 71
  d₂ := 82

end CFSG.SectionRank.QTK.CoverB
