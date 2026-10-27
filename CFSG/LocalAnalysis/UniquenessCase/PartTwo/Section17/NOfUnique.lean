module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.ComponentClassification.EvenLieFieldExponent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeafProof (IsChar2LieShape)

variable {G : Type} [Group G]

theorem isChar2LieShape_PSU_four : IsChar2LieShape .PSU 4 :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))


theorem nOf_eq_of_isChar2LieShape {L : Subgroup G} {t : StatedLieTag} {m f : ℕ}
    (h : CFSG.Blueprint.LieModel (Bar2 L) t m 2 f) (hshape : IsChar2LieShape t m) :
    nOf L = f := by
  have hf : 0 < f := (CFSG.Blueprint.LieModel.admissible h).2.1
  have hmem : f ∈ {f' : ℕ | 0 < f' ∧
      ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ),
        CFSG.Blueprint.LieModel (Bar2 L) t m 2 f'} := ⟨hf, t, m, h⟩
  unfold nOf
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨f, hmem⟩ ?_)
  rintro f' ⟨-, t', m', h'⟩
  have hff := (CFSG.ComponentClassification.CatLeafProof.lieModel_eq_of_isChar2LieShape
    h hshape h').2.2
  omega

theorem nOf_eq_of_isU4 {L : Subgroup G} {n : ℕ} (h : IsU4 (Bar2 L) n) : nOf L = n :=
  nOf_eq_of_isChar2LieShape h isChar2LieShape_PSU_four

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
