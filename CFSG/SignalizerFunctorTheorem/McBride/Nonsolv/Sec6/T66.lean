module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T65
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L63
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66.KDown
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66.NS

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem theorem_6_6_a
    (h : Counterexample p A θ) :
    ∀ X ∈ Msig p A (thetaNs p A θ), X = ⊥ := by
  obtain ⟨hfun, hC, W, hW, hWmax⟩ := h.theorem_6_5_a
  intro X hX
  suffices hW0 : W = ⊥ from le_bot_iff.mp (hW0 ▸ hWmax X hX)
  by_contra hW1
  have hWθ : W ∈ Msig p A θ :=
    signalizers_mono_functor (fun a ha ha1 => h.thetaNs_le ha ha1) hW
  have hB : ∀ B ∈ signalizerFunctorEk p 2 A,
      kOf (thetaOf θ B) ≤ Subgroup.normalizer (W : Set G) := by
    intro B hB
    have hBA := hB.1
    have hWgen : W = ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), thetaNs p A θ b := by
      apply le_antisymm
      · calc W = ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), W ⊓ Subgroup.centralizer {b} :=
              (iSup_inf_centralizer h.prime (h.isElemAbelian_of_le hBA) hB.2.ge
                (hBA.trans hW.1) hW.2.1).symm
          _ ≤ _ := by
            refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
            exact (hW.2.2.1 b (hBA hb) hb1).trans
              (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl)))
      · exact iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 =>
          hWmax _ (hfun.apply_mem_signalizers (hBA hb) hb1 (hC b (hBA hb) hb1))
    rw [hWgen]
    refine CFSG.SignalizerFunctor.Helpers.normalizer_iSup_of_le _ _ fun b => ?_
    refine CFSG.SignalizerFunctor.Helpers.normalizer_iSup_of_le _ _ fun hb => ?_
    refine CFSG.SignalizerFunctor.Helpers.normalizer_iSup_of_le _ _ fun hb1 => ?_
    refine h.theorem_6_5_b (hBA hb) hb1 ⟨(kOf_le _).trans (thetaOf_le_apply hb hb1), ?_, ?_⟩
      (kOf_kOf _)
    · rw [h.isFunctor.inf_centralizer_self (hBA hb) hb1]
      exact (thetaOf_anti hBA).trans (le_normalizer_kOf _)
    · exact le_normalizer_kOf_of_le_normalizer (h.isFunctor.normalizes_thetaOf hBA)
  obtain ⟨Y, hY, hYN, hYmax⟩ := h.locallyComplete W hWθ hW1
  obtain ⟨B, hB2, hBY⟩ := (h.lemma_6_3 hY).2
  exact hBY (hYmax _ (kOf_mem_msig (h.thetaOf_mem_msig hB2.1 (h.ne_bot_of_mem_E2 hB2)))
    (hB B hB2))

theorem theorem_6_6_b
    (h : Counterexample p A θ) {X : Subgroup G} (hX : X ∈ Msig p A θ)
    (hD : thetaOf θ A ≤ X) : kDown X A = ⊥ :=
  T66.kDown_eq_bot_of_forall_nsSet ⟨h.prime, h.elemAbelian, hX.1, hX.2.2.2⟩ fun _ hY =>
    h.theorem_6_6_a _ (h.mem_msig_thetaNs_of_mem_nsSet hX hD hY)

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
