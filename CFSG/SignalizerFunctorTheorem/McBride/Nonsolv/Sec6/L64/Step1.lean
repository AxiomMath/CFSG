module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Restrict

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem eq_one_of_mem_centralizer_sSup_msig (h : Counterexample p A θ) {a : G} (ha : a ∈ A)
    (hc : a ∈ Subgroup.centralizer ((sSup (Msig p A θ) : Subgroup G) : Set G)) : a = 1 := by
  by_contra ha1
  refine h.notComplete ⟨θ a, h.apply_mem_msig ha ha1, fun X hX x hx => ?_⟩
  refine hX.2.2.1 a ha ha1 (Subgroup.mem_inf.mpr ⟨hx, ?_⟩)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hc x (le_sSup hX hx)

theorem normalizer_eq_top_of_generated (h : Counterexample p A θ) {M U : Subgroup G}
    (hWM : sSup (Msig p A θ) ≤ Subgroup.normalizer (M : Set G)) (hU : U ∈ Msig p A θ)
    (hgen : ∀ b ∈ A, b ≠ 1 → θ b ⊓ M ≤ U)
    (hfix : ∀ b ∈ A, b ≠ 1 → U ⊓ Subgroup.centralizer {b} ≤ θ b ⊓ M) :
    Subgroup.normalizer (U : Set G) = ⊤ := by
  have hB : ∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 →
      thetaOf θ B ≤ Subgroup.normalizer (U : Set G) := by
    intro B hBA hBc
    have hU' : (⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), θ b ⊓ M) = U := by
      refine le_antisymm ?_ ?_
      · exact iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => hgen b (hBA hb) hb1
      · calc U = ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), U ⊓ Subgroup.centralizer {b} :=
              (iSup_inf_centralizer h.prime (h.isElemAbelian_of_le hBA) hBc.ge
                (hBA.trans hU.1) hU.2.1).symm
          _ ≤ _ := iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 =>
              (hfix b (hBA hb) hb1).trans
                (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl)))
    rw [← hU']
    refine CFSG.SignalizerFunctor.Helpers.normalizer_iSup_of_le _ _ fun b => ?_
    refine CFSG.SignalizerFunctor.Helpers.normalizer_iSup_of_le _ _ fun hb => ?_
    refine CFSG.SignalizerFunctor.Helpers.normalizer_iSup_of_le _ _ fun hb1 => ?_
    have hle : thetaOf θ B ≤ θ b := thetaOf_le_apply hb hb1
    have hθb : θ b ≤ sSup (Msig p A θ) := h.apply_le_sSup_msig (hBA hb) hb1
    exact (le_inf (hle.trans Subgroup.le_normalizer) (hle.trans (hθb.trans hWM))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hW : sSup (Msig p A θ) ≤ Subgroup.normalizer (U : Set G) := by
    rw [h.sSup_msig_eq_thetaSup]
    refine thetaSup_le fun a ha ha1 => ?_
    rw [h.isFunctor.apply_eq_iSup_thetaOf h.prime h.elemAbelian h.rank_three_le ha ha1]
    exact iSup_le fun B => iSup_le fun hBA => iSup_le fun hBc => iSup_le fun _ => hB B hBA hBc
  rw [eq_top_iff, ← h.generation]
  exact sup_le hW hU.1

theorem exists_normal_member_of_normal (h : Counterexample p A θ) {M : Subgroup G}
    (hMW : M ≤ sSup (Msig p A θ)) (hMn : (M.subgroupOf (sSup (Msig p A θ))).Normal)
    (hMA : A ≤ Subgroup.normalizer (M : Set G)) (hMne : M ≠ sSup (Msig p A θ)) :
    ∃ U ∈ Msig p A θ, U.Normal ∧ ∀ a ∈ A, a ≠ 1 → θ a ⊓ M ≤ U := by
  have hex : ∃ a ∈ A, a ≠ 1 ∧ ¬ θ a ≤ M := by
    by_contra! hcon
    refine hMne (le_antisymm hMW ?_)
    rw [h.sSup_msig_eq_thetaSup]
    exact thetaSup_le hcon
  have hθM : IsFunctor p A (restrictFunctor M θ) := h.isFunctor.restrictFunctor hMA
  have hCM : ∀ a ∈ A, a ≠ 1 → signalizerMcBrideHypothesisB p (restrictFunctor M θ a) :=
    fun a ha ha1 => hypB_mono inf_le_left (h.hypC a ha ha1)
  obtain ⟨U, hU, hUmax⟩ := h.hmin _ hθM hCM (size_restrictFunctor_lt hex)
  have hUθ : U ∈ Msig p A θ := signalizers_mono_functor (fun a _ _ => inf_le_left) hU
  have hgen : ∀ b ∈ A, b ≠ 1 → θ b ⊓ M ≤ U := fun b hb hb1 =>
    hUmax _ (hθM.apply_mem_signalizers hb hb1 (hCM b hb hb1))
  have hfix : ∀ b ∈ A, b ≠ 1 → U ⊓ Subgroup.centralizer {b} ≤ θ b ⊓ M := fun b hb hb1 =>
    hU.2.2.1 b hb hb1
  have hWM : sSup (Msig p A θ) ≤ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMW).mp hMn
  exact ⟨U, hUθ, Subgroup.normalizer_eq_top_iff.mp
    (h.normalizer_eq_top_of_generated hWM hUθ hgen hfix), hgen⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
