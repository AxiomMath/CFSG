module

public import CFSG.OddTranspositions.HypothesisC

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem not_commute_of_mem_AalphaStar (hC : HypothesisC D) {x a : G}
    (hx : x ∈ AalphaStar D hC.alpha) (ha : a ∈ hC.alpha) : ¬ Commute x a := by
  rintro h
  obtain ⟨β, hβ, hxβ⟩ := hx
  obtain ⟨hβclass, hβnotperp⟩ := mem_Aalpha_iff.mp hβ
  obtain ⟨g, rfl⟩ := mem_blockClass_iff'.mp hβclass
  have hne : g • hC.alpha ≠ hC.alpha := by
    intro hEq
    exact hβnotperp (mem_perp_iff.mpr (Or.inr hEq))
  have hall := commute_block_of_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha hne ha hxβ h.symm
  have hβD : (g • hC.alpha : Set G) ⊆ D := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    simpa [ConjAct.smul_def] using
      hC.setup.normal (ConjAct.ofConjAct g) z (hC.isBlock_alpha.subset hz)
  have hβDalpha : (g • hC.alpha) ∈ Dalpha D hC.alpha :=
    mem_Dalpha_iff.mpr ⟨hβclass, hβD, hne, fun a' ha' b hb => hall a' ha' b hb⟩
  exact hβnotperp (mem_perp_iff.mpr (Or.inl hβDalpha))

end CFSG.OddTranspositions
