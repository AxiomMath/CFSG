module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBRealCheck
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.SectionRank.QTK.CoverB

open CFSG.SectionRank.Native

@[expose] def j3RealProg : List Op := [
    .pow 2 1 2, .mul 1 0 3, .mul 3 1 4, .mul 4 0 5, .mul 5 2 6, .mul 6 0 7, .mul 7 2 8, .mul 8 0 9,
    .mul 9 1 10, .mul 2 0 11, .mul 11 1 12, .mul 12 0 13, .mul 13 1 14, .mul 14 0 15,
    .mul 15 2 16, .mul 16 0 17, .mul 17 2 18, .mul 10 0 19, .mul 19 18 20, .mul 0 20 21,
    .pow 4 21 22, .pow 6 21 23]

@[expose] def j3Real : RealData where
  base :=
    { seedA := include_str "../../CFSG/Blueprint/Data/J3G1-f2r80B0.m1"
      seedB := include_str "../../CFSG/Blueprint/Data/J3G1-f2r80B0.m2"
      nregs := 24
      prog := j3RealProg
      outs := []
      tests := [ 0 ] }
  t₁ := 23
  t₂ := 23
  x := 22
  d := 0
  a := 0
  b := 1
  dord := 2

end CFSG.SectionRank.QTK.CoverB
