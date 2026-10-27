module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem CFSG.ClassicalInvolution.ModelFacts

variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ} (hR : TauCeti.IsFiniteType R)

theorem isRt_iff_mem_roots {v : ι → ℤ} : IsRt hR v ↔ v ∈ roots hR ∅ := by
  constructor
  · rintro ⟨w, j, h⟩
    exact Or.inl ⟨w, j, h.symm⟩
  · rintro (⟨w, j, h⟩ | ⟨w, j, hj, h⟩)
    · exact ⟨w, j, h.symm⟩
    · exact absurd hj (Set.notMem_empty j)

theorem exists_weylAction_eq_of_isRt (hirr : IsIrreducible R) {α β : ι → ℤ} (hα : IsRt hR α)
    (hβ : IsRt hR β)
    (h : form hR (toRat α) (toRat α) = form hR (toRat β) (toRat β)) :
    ∃ w : Wg hR, weylAction hR w α = β :=
  exists_weylAction_eq_of_lenSq_eq hR hirr ((isRt_iff_mem_roots hR).1 hα)
    ((isRt_iff_mem_roots hR).1 hβ) h

end CFSG.StandardType.LevTwo
