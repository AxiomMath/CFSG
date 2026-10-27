module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5CfgComp
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

namespace Cfg145

variable {K : Type} [Group K] [Finite K] {M X₁ X₂ P : Subgroup K}

theorem oneComp (c : Cfg145 M X₁ X₂ P) {J : Subgroup K} (hJ : IsComponentOf J ⊤)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J) (hXJ : X₁ ⊔ X₂ ≤ J) :
    K330Cfg.OneComp J M (X₁ ⊔ X₂) P := by
  have hne : X₁ ≠ X₂ := by
    intro h
    have hinf : X₁ ⊓ X₂ = X₁ := by rw [← h, inf_idem]
    rw [c.inf_eq_bot] at hinf
    have hcard : Nat.card X₁ = 1 := by rw [← hinf, Subgroup.card_bot]
    rw [c.card_left] at hcard
    norm_num at hcard
  refine ⟨c.isKGroup, ?_, c.isSimpleGroup_of_isComponentOf hJ, ?_,
    c.isSylowOf_three.of_le hXJ le_top, c.isElemAbelian, c.card_sup, c.strong, c.normalizer_le,
    c.isSylowOf_seven, c.le_centralizer, c.isCyclic,
    ⟨X₁, X₂, le_sup_left, le_sup_right, c.card_left, c.card_right, hne, c.permutes⟩,
    c.exists_isSylowOf_two⟩
  · refine ⟨fun n hn g => ?_⟩
    have hmap := hJu _ (isComponentOf_map_conj hJ g)
    have hmem : g * n * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom :=
      ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rwa [hmap] at hmem
  · rw [← layer_eq_of_forall hJ hJu]
    exact c.centralizer_layer_eq_bot

end Cfg145

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
