module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem conjSubgroup_le_pCoreOf_of_le_S_of_ne (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (h10 : ∀ x : G, conjSubgroup V x ≤ S → ¬ conjSubgroup V x ≤ kerMOf M H →
      conjSubgroup V x = V)
    (h56 : ∀ y ∈ H, conjSubgroup V y ≤ S → conjSubgroup V y = V)
    {z : G} (hzS : conjSubgroup V z ≤ S) (hz : conjSubgroup V z ≠ V) :
    conjSubgroup V z ≤ pCoreOf 2 H := by
  by_contra hzO
  obtain ⟨k, hk, hkS, hkk⟩ :=
    IsMinFam16.exists_conj_le_S_not_le_kerMOf h1 hS h hH (hzS.trans hH.1.1) hzO
  have hk10 : conjSubgroup V (z * k) = V := h10 (z * k) hkS hkk
  have heq : conjSubgroup V z = conjSubgroup V k⁻¹ := by
    rw [show z = (z * k) * k⁻¹ by group, ← conjSubgroup_conjSubgroup, hk10]
  exact hz (heq.trans (h56 k⁻¹ (H.inv_mem hk) (heq ▸ hzS)))

theorem IsMinFam16.conj_eq_of_le_S (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (h10 : ∀ x : G, conjSubgroup V x ≤ S → ¬ conjSubgroup V x ≤ kerMOf M H →
      conjSubgroup V x = V)
    (h56 : ∀ y ∈ H, conjSubgroup V y ≤ S → conjSubgroup V y = V) {y : G}
    (hy : conjSubgroup V y ≤ S) : conjSubgroup V y = V := by
  by_contra hne
  let Γ : Set (Subgroup G) := {Z | (∃ z : G, Z = conjSubgroup V z) ∧ Z ≤ S ∧ Z ≠ V}
  let s : Set G := {x : G | ∃ Z ∈ Γ, x ∈ Z}
  let R : Subgroup G := Subgroup.closure s
  have hyΓ : conjSubgroup V y ∈ Γ := ⟨⟨y, rfl⟩, hy, hne⟩
  have hA_le_R : conjSubgroup V y ≤ R := fun x hx =>
    Subgroup.subset_closure (show x ∈ s from ⟨conjSubgroup V y, hyΓ, hx⟩)
  have hGamma_pCore : ∀ Z ∈ Γ, Z ≤ pCoreOf 2 H := by
    intro Z hZ
    change (∃ z : G, Z = conjSubgroup V z) ∧ Z ≤ S ∧ Z ≠ V at hZ
    obtain ⟨⟨z, rfl⟩, hZS, hZne⟩ := hZ
    exact conjSubgroup_le_pCoreOf_of_le_S_of_ne h1 hS h hH hV h10 h56 hZS hZne
  have hR_pCore : R ≤ pCoreOf 2 H := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨Z, hZΓ, hxZ⟩ := hx
    exact hGamma_pCore Z hZΓ hxZ
  have hR2 : IsPGroup 2 R :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le hR_pCore
  have hRne : R ≠ ⊥ := by
    intro hb
    have hAle : conjSubgroup V y ≤ ⊥ := hA_le_R.trans (le_of_eq hb)
    have hAbot : conjSubgroup V y = ⊥ := le_bot_iff.1 hAle
    have hVbot : V = ⊥ := by
      calc V = conjSubgroup (conjSubgroup V y) y⁻¹ := by
              rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
        _ = ⊥ := by rw [hAbot, E3.conjSubgroup_bot]
    exact h.hyp.ne_bot (le_bot_iff.1 (hVbot ▸ h.hyp.h6.le))
  have hHleNR : H ≤ Subgroup.normalizer (R : Set G) := by
    refine Subgroup.le_normalizer_closure_iff.mpr fun h' hh z hz => ?_
    change ∃ Z : Subgroup G, Z ∈ Γ ∧ z ∈ Z at hz
    obtain ⟨Z, hZΓ, hzZ⟩ := hz
    change (∃ w : G, Z = conjSubgroup V w) ∧ Z ≤ S ∧ Z ≠ V at hZΓ
    obtain ⟨⟨w, rfl⟩, hZS, hZne⟩ := hZΓ
    have hZ_O : conjSubgroup V w ≤ pCoreOf 2 H :=
      conjSubgroup_le_pCoreOf_of_le_S_of_ne h1 hS h hH hV h10 h56 hZS hZne
    have hconj_le_O : conjSubgroup (conjSubgroup V w) h'⁻¹ ≤ pCoreOf 2 H :=
      (E3.conjSubgroup_mono_left h'⁻¹ hZ_O).trans
        (le_of_eq (conjSubgroup_eq_iff_mem_normalizer.mpr
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H (H.inv_mem hh))))
    have hconj_ne : conjSubgroup (conjSubgroup V w) h'⁻¹ ≠ V := by
      intro heqV
      exact hV (heqV ▸ hconj_le_O)
    have hconjΓ : conjSubgroup (conjSubgroup V w) h'⁻¹ ∈ Γ :=
      ⟨⟨w * h'⁻¹, by rw [conjSubgroup_conjSubgroup]⟩,
        hconj_le_O.trans (Cex16.pCoreOf_le_S h1 hS h hH.1), hconj_ne⟩
    have hconj_mem : h' * z * h'⁻¹ ∈ conjSubgroup (conjSubgroup V w) h'⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have hgrp : h'⁻¹ * (h' * z * h'⁻¹) * (h'⁻¹)⁻¹ = z := by group
      rwa [hgrp]
    exact Subgroup.subset_closure ⟨_, hconjΓ, hconj_mem⟩
  have hXleNR : M ⊓ Subgroup.normalizer (E3.wClos V 0 S : Set G) ≤
      Subgroup.normalizer (R : Set G) := by
    refine Subgroup.le_normalizer_closure_iff.mpr fun n hn z hz => ?_
    obtain ⟨hnM, hnW⟩ := hn
    change ∃ Z : Subgroup G, Z ∈ Γ ∧ z ∈ Z at hz
    obtain ⟨Z, hZΓ, hzZ⟩ := hz
    change (∃ w : G, Z = conjSubgroup V w) ∧ Z ≤ S ∧ Z ≠ V at hZΓ
    obtain ⟨⟨w, rfl⟩, hZS, hZne⟩ := hZΓ
    have hZW : conjSubgroup V w ≤ E3.wClos V 0 S := by
      refine E3.le_wClos ⟨hZS, w, le_rfl, ?_⟩
      exact E3.mQuot_self _
    have hnV : conjSubgroup V n = V :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (by rw [h.hyp.h6.normalizer_eq]; exact hnM)
    have hconjW : conjSubgroup (E3.wClos V 0 S) n⁻¹ = E3.wClos V 0 S :=
      conjSubgroup_eq_iff_mem_normalizer.mpr
        ((Subgroup.normalizer (E3.wClos V 0 S : Set G)).inv_mem hnW)
    have hconj_le_W : conjSubgroup (conjSubgroup V w) n⁻¹ ≤ E3.wClos V 0 S :=
      (E3.conjSubgroup_mono_left n⁻¹ hZW).trans (le_of_eq hconjW)
    have hconj_ne : conjSubgroup (conjSubgroup V w) n⁻¹ ≠ V := by
      intro heqV
      have hcong := congrArg (fun A : Subgroup G => conjSubgroup A n) heqV
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, hnV] at hcong
      exact hZne hcong
    have hconjΓ : conjSubgroup (conjSubgroup V w) n⁻¹ ∈ Γ :=
      ⟨⟨w * n⁻¹, by rw [conjSubgroup_conjSubgroup]⟩,
        hconj_le_W.trans (E3.wClos_le 0 S), hconj_ne⟩
    have hconj_mem : n * z * n⁻¹ ∈ conjSubgroup (conjSubgroup V w) n⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have hgrp : n⁻¹ * (n * z * n⁻¹) * (n⁻¹)⁻¹ = z := by group
      rwa [hgrp]
    exact Subgroup.subset_closure ⟨_, hconjΓ, hconj_mem⟩
  have hNRleM : Subgroup.normalizer (R : Set G) ≤ M :=
    normalizer_le_of_inCalU (h.uniqueMax_normalizer_wClos h1 hS) hXleNR hRne hR2
  exact hH.1.2.2 (hHleNR.trans hNRleM)

theorem Cex16.wClos_eq_of_forall (h : Cex16 M V₀ V U S)
    (hall : ∀ y : G, conjSubgroup V y ≤ S → conjSubgroup V y = V) : E3.wClos V 0 S = V := by
  refine le_antisymm ?_ (Cex16.V_le_wClos h)
  refine E3.wClos_le_of_forall fun A hA => ?_
  rw [E3.mem_gammaSet_iff] at hA
  obtain ⟨hAS, g, hAg, hm0⟩ := hA
  have hVp : IsPGroup 2 (conjSubgroup V g) := E3.isPGroup_conjSubgroup h.hyp.isPGroup g
  have hAeq : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hVp hAg).1 hm0
  rw [hAeq]
  exact le_of_eq (hall g (hAeq ▸ hAS))

end CFSG.LocalAnalysis.WeakClosure81

end
