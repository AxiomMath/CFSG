module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUnique

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeafProof (IsChar2LieShape)

variable {G : Type} [Group G]

theorem isChar2LieShape_twistedB2 : IsChar2LieShape .twistedB2 0 :=
  Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem isChar2LieShape_PSp : IsChar2LieShape .PSp 2 :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))


theorem nOf_eq_of_isSz {L : Subgroup G} {n : ℕ} (h : IsSz (Bar2 L) n) : nOf L = n :=
  nOf_eq_of_isChar2LieShape h isChar2LieShape_twistedB2

theorem nOf_eq_of_isSp4 {L : Subgroup G} {n : ℕ} (h : IsSp4 (Bar2 L) n) : nOf L = n :=
  nOf_eq_of_isChar2LieShape h isChar2LieShape_PSp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
