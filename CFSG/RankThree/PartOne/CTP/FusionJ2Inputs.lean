module

public import CFSG.RankThree.PartOne.CTP.FusionDefs

public section

namespace CFSG.RankThree.PartOne.CTP.Fus

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def j2Fus : Spec where
  p := 5
  rA := 0
  oA := 2
  rB := 1
  oB := 3
  rx := 14
  ry := 15
  tx := 0
  gens := [
    ⟨2, 2, [(14, 1)], [(15, 4)], 0⟩,
    ⟨17, 2, [(15, 4)], [(14, 1)], 0⟩,
    ⟨3, 6, [(14, 1)], [(15, 4)], 0⟩,
    ⟨18, 6, [(15, 4)], [(14, 1)], 0⟩,
    ⟨21, 2, [(14, 1)], [(15, 1)], 0⟩,
    ⟨22, 2, [(15, 1)], [(14, 1)], 0⟩,
    ⟨23, 12, [(14, 1)], [(15, 4)], 0⟩,
    ⟨24, 12, [(15, 4)], [(14, 1)], 0⟩,
    ⟨25, 2, [(14, 1)], [(14, 4)], 0⟩,
    ⟨26, 2, [(14, 4)], [(14, 1)], 0⟩]
  wA := [
    (21, 1), (18, 1), (23, 1), (3, 1), (23, 1), (18, 1), (25, 1)]
  wB := [
    (21, 1), (3, 1), (24, 1), (18, 1), (24, 1), (3, 1), (25, 1)]

@[expose] def j2FusN : Nat := 27

@[expose] def j2FusProg : List Op := [
    .pow 1 0 2, .pow 1 1 3, .mul 2 3 4, .mul 4 3 5, .mul 4 5 6, .mul 4 6 7, .mul 7 4 8,
    .mul 8 5 9, .mul 4 9 10, .mul 10 5 11, .pow 6 6 2, .mul 6 6 7, .mul 7 4 8, .mul 8 4 9,
    .mul 4 11 7, .mul 5 6 8, .mul 7 8 10, .pow 11 9 8, .mul 8 10 11, .mul 11 9 3, .pow 1 2 12,
    .pow 5 3 13, .pow 1 2 16, .mul 16 3 16, .pow 2 16 14, .pow 1 2 16, .mul 16 13 16,
    .pow 2 16 15, .pow 1 2 17, .pow 5 3 18, .pow 1 0 19, .pow 2 1 20, .pow 1 19 21, .mul 21 1 21,
    .mul 21 19 21, .mul 21 20 21, .mul 21 0 21, .pow 1 21 22, .pow 1 1 23, .mul 23 19 23,
    .mul 23 1 23, .mul 23 0 23, .mul 23 1 23, .mul 23 19 23, .mul 23 1 23, .pow 11 23 24,
    .pow 1 19 25, .mul 25 1 25, .mul 25 19 25, .mul 25 1 25, .mul 25 0 25, .mul 25 1 25,
    .mul 25 1 25, .mul 25 19 25, .mul 25 20 25, .mul 25 0 25, .pow 1 25 26]

end CFSG.RankThree.PartOne.CTP.Fus
