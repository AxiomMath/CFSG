module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBSignedCheck
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.SectionRank.QTK.CoverB

open CFSG.SectionRank.Native

@[expose] def mclSignedProg : List Op := [
    .pow 3 1 3, .pow 2 1 4, .mul 4 0 2, .mul 2 3 5, .mul 0 5 2, .mul 2 0 6, .pow 4 1 7, .mul 1 6 2,
    .mul 2 7 8, .mul 0 8 2, .mul 2 0 9, .mul 3 9 2, .mul 2 4 10, .mul 0 10 2, .mul 2 0 11,
    .mul 7 11 2, .mul 2 1 12, .mul 0 12 2, .mul 2 0 13, .mul 1 13 2, .mul 2 7 14, .mul 4 9 2,
    .mul 2 3 15, .mul 0 15 2, .mul 2 0 16, .mul 1 16 2, .mul 2 7 17, .mul 0 17 2, .mul 2 0 18,
    .mul 7 18 2, .mul 2 1 19, .mul 3 0 2, .mul 2 4 20, .mul 0 20 2, .mul 2 0 21, .mul 7 21 2,
    .mul 2 1 22, .mul 0 22 2, .mul 2 0 23, .mul 1 23 2, .mul 2 7 24, .mul 0 24 2, .mul 2 0 25,
    .mul 4 25 2, .mul 2 3 26, .mul 3 21 2, .mul 2 4 27, .mul 0 27 2, .mul 2 0 28, .mul 4 28 2,
    .mul 2 3 29, .mul 0 29 2, .mul 2 0 30, .mul 4 30 2, .mul 2 3 31, .mul 14 19 32, .mul 26 31 33]

@[expose] def mclSigned : SignedData where
  base :=
    { seedA := include_str "../../CFSG/Blueprint/Data/McLG1-f3r21B0.m1"
      seedB := include_str "../../CFSG/Blueprint/Data/McLG1-f3r21B0.m2"
      nregs := 34
      prog := mclSignedProg
      outs := []
      tests := [0] }
  t₁ := 0
  t₂ := 0
  a := 32
  b := 33
  d₁ := 14
  d₂ := 26

end CFSG.SectionRank.QTK.CoverB
