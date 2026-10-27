module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUnique

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeafProof (IsChar2LieShape)

variable {G : Type} [Group G]

theorem isChar2LieShape_PSL : IsChar2LieShape .PSL 2 := Or.inl ⟨rfl, rfl⟩

theorem isChar2LieShape_G2 : IsChar2LieShape .G2 0 :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))


theorem nOf_eq_of_isL2 {L : Subgroup G} {n : ℕ} (h : IsL2 (Bar2 L) n) : nOf L = n :=
  nOf_eq_of_isChar2LieShape h isChar2LieShape_PSL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
