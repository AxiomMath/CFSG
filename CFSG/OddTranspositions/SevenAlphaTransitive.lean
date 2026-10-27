module

public import CFSG.OddTranspositions.HypothesisC

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem normalizer_transitive_alpha (hC : HypothesisC D) {u v : G}
    (hu : u ∈ hC.alpha) (hv : v ∈ hC.alpha) :
    ∃ g ∈ Subgroup.normalizer hC.alpha, g * u * g⁻¹ = v := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_isClass hC.setup.isClass
    (hC.isBlock_alpha.subset hu) (hC.isBlock_alpha.subset hv))
  refine ⟨g, ?_, hg⟩
  have hmem : ConjAct.toConjAct g • u ∈ hC.alpha := by
    rw [ConjAct.toConjAct_smul]
    rw [hg]
    exact hv
  have hsm : ConjAct.toConjAct g • hC.alpha = hC.alpha :=
    MulAction.IsBlock.smul_eq_of_mem hC.isBlock_alpha.isBlock hu hmem
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have himg : ConjAct.toConjAct g • hC.alpha = MulAut.conj g '' hC.alpha := by
    rw [← Set.image_smul]
    rfl
  rwa [himg] at hsm

end CFSG.OddTranspositions
