module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L63
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L68.Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L68.Claim

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L68

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem kOf_thetaOf_le_normalizer
    (h : Counterexample p A θ) {J W : Subgroup G}
    (hJ : J ∈ lcal (thetaOf θ A)) (hW : IsGreatestCentralizing p A θ J W) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) :
    kOf (thetaOf θ B) ≤ Subgroup.normalizer (W : Set G) := by
  have hsolB := sol_thetaOf h hB.1 (h.ne_bot_of_mem_E2 hB)
  rw [← (isDirectProduct_lcal_kOf hsolB).sSup_eq]
  refine sSup_le fun L hL => ?_
  rcases le_or_le_centralizer h hJ hW hB hL with hle | hle
  · exact hle.trans Subgroup.le_normalizer
  · exact hle.trans (Subgroup.centralizer_le_normalizer _)

theorem eq_bot
    (h : Counterexample p A θ) {J W : Subgroup G} (hJ : J ∈ lcal (thetaOf θ A))
    (hW : IsGreatestCentralizing p A θ J W) : W = ⊥ := by
  by_contra hW1
  obtain ⟨Y, hY, -, hYmax⟩ := h.locallyComplete W hW.mem hW1
  obtain ⟨B, hB, hBY⟩ := (h.lemma_6_3 hY).2
  exact hBY (hYmax _ (kOf_mem_msig (h.thetaOf_mem_msig hB.1 (h.ne_bot_of_mem_E2 hB)))
    (kOf_thetaOf_le_normalizer h hJ hW hB))

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L68
