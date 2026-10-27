module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup

import CFSG.GroupTheory.BaerSuzukiCentralize
import CFSG.LargeExtraspecial.AS35QCoLin
import CFSG.LargeExtraspecial.AS35ZSDefs
import CFSG.LargeExtraspecial.OrthoF2Inverted
import CFSG.LargeExtraspecial.OrthoF2PairsCases
import CFSG.LinearAlgebra.F2PlaneMaps
import CFSG.RankThree.GF2n.Stroth78.Sec2Five
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
public import CFSG.GroupTheory.OddOrderClosureIdempotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem commSpace_rhoLin_eq_sup_of_orderOf_mul_eq_three (S : Setting z E F) {β γ ω : Hbar z}
    (hβA2 : β ∈ A2set S) (hγA2 : γ ∈ A2set S) (hω : ω = β * γ)
    (h3 : orderOf (β * γ) = 3) :
    commSpace (rhoLin S ω) = commSpace (rhoLin S β) ⊔ commSpace (rhoLin S γ) := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  haveI : Finite (Additive (QbarOf S)) := inferInstance
  haveI : Module.Finite (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have h3ρ : orderOf (rhoLin S β * rhoLin S γ) = 3 := by
    rw [← rhoLin_mul]
    simpa [rhoLin, h3] using orderOf_rhoBar S (β * γ)
  have h := CFSG.LargeExtraspecial.commSpace_mul_of_orderOf_eq_three (q := qS S)
    (hq := q_nondegenerate S)
    (hα := by simpa [rhoLin] using isTypeA_rhoBar_of_isA2Hbar S hβA2)
    (hβ := by simpa [rhoLin] using isTypeA_rhoBar_of_isA2Hbar S hγA2) h3ρ
  rw [hω, rhoLin_mul]
  exact h.2.1

theorem commSpace_le_fixSpace_of_mem_kernelTwo (S : Setting z E F) (a : G) {β γ ω : Hbar z}
    (hβA2 : β ∈ A2set S) (hγcomp : γ ∈ ncComp (A2set S) β) (hω : ω = β * γ)
    (hγω : γ = ω * β * ω⁻¹) (h3 : orderOf (β * γ) = 3) :
    ∀ k ∈ kernelTwo S a β, commSpace (rhoLin S k) ≤ fixSpace (rhoLin S ω) := by
  haveI : Finite (Additive (QbarOf S)) := inferInstance
  haveI : Module.Finite (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hγA2 : γ ∈ A2set S := CFSG.Timmesfeld.ncComp_subset hβA2 hγcomp
  have hωeq : commSpace (rhoLin S ω) =
      commSpace (rhoLin S β) ⊔ commSpace (rhoLin S γ) :=
    commSpace_rhoLin_eq_sup_of_orderOf_mul_eq_three S hβA2 hγA2 hω h3
  have h3ω : orderOf (rhoLin S ω) = 3 := by
    rw [hω, rhoLin_mul]
    simpa [rhoLin, h3] using orderOf_rhoBar S (β * γ)
  have hγdecomp : rhoLin S γ = rhoLin S ω * rhoLin S β * (rhoLin S ω)⁻¹ := by
    rw [hγω]
    simp only [rhoLin_mul, rhoLin_inv]
  have hγmap : commSpace (rhoLin S γ) =
      (commSpace (rhoLin S β)).map
        (rhoLin S ω : Additive (QbarOf S) →ₗ[ZMod 2] Additive (QbarOf S)) := by
    rw [hγdecomp, CFSG.LargeExtraspecial.AS35QCo.commSpace_conj]
  intro k hk
  have hkβ : k * β = β * k :=
    commute_closure_Eset_diff_ncComp S a hβA2 k hk.1 β
      (Subgroup.subset_closure (CFSG.Timmesfeld.mem_ncComp_self (A2set S) β))
  have hkγ : k * γ = γ * k :=
    commute_closure_Eset_diff_ncComp S a hβA2 k hk.1 γ (Subgroup.subset_closure hγcomp)
  have hkω : k * ω = ω * k := by
    rw [hω]
    calc k * (β * γ) = k * β * γ := by rw [mul_assoc]
      _ = β * k * γ := by rw [hkβ]
      _ = β * (k * γ) := by rw [mul_assoc]
      _ = β * (γ * k) := by rw [hkγ]
      _ = β * γ * k := by rw [mul_assoc]
  have hcommρ : rhoLin S k * rhoLin S ω = rhoLin S ω * rhoLin S k := by
    have := congrArg (rhoLin S) hkω
    simpa [rhoLin_mul] using this
  have hfixγ : ∀ v ∈ commSpace (rhoLin S γ), rhoLin S k v = v := by
    intro v hv
    rw [hγmap] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    calc rhoLin S k (rhoLin S ω w) = (rhoLin S k * rhoLin S ω) w := by simp
      _ = (rhoLin S ω * rhoLin S k) w := by rw [hcommρ]
      _ = rhoLin S ω (rhoLin S k w) := by simp
      _ = rhoLin S ω w := by rw [hk.2 w hw]
  refine CFSG.LargeExtraspecial.commSpace_le_fixSpace_of_commute (ω := rhoLin S ω)
    (y := rhoLin S k) ?_ hcommρ ?_
  · rw [h3ω]
    exact ⟨1, by norm_num⟩
  · intro v hv
    rw [hωeq] at hv
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hk.2 v₁ hv₁, hfixγ v₂ hv₂]

theorem commute_of_mem_Rbar_of_mem_kernelTwo (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {β : Hbar z} (hβR : β ∈ Rbar S a) (hβ1 : β ≠ 1)
    {r : Hbar z} (hr : r ∈ Rbar S a) {k : Hbar z} (hk : k ∈ kernelTwo S a β) :
    r * k = k * r := by
  have hβA2 : β ∈ A2set S :=
    Tset_subset_A2set S a (h.mem_Tset_of_mem_Rbar hβR hβ1)
  have hrβ : r * β = β * r :=
    commute_of_mem_Lbar S h.mem_Q h.isConj (Rbar_le_Lbar S a hr) (Rbar_le_Lbar S a hβR)
  have hr2 : r * r = 1 := by
    rw [← pow_two]
    exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj (Rbar_le_Lbar S a hr)
  have hK : ∀ P : Subgroup (Hbar z), P ≤ kernelTwo S a β → IsPGroup 2 P →
      kernelTwo S a β ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥ :=
    fun P hP hPg hN => eq_bot_of_le_kernelTwo S a hβA2 P hP hPg hN
  have hNK : r ∈ Subgroup.normalizer (kernelTwo S a β : Set (Hbar z)) :=
    mem_normalizer_kernelTwo_of_commute S a hβA2 hrβ
  have htK : ∀ y ∈ kernelTwo S a β, r * y * r⁻¹ ∈ kernelTwo S a β :=
    fun y hy => (Subgroup.mem_normalizer_iff.mp hNK y).mp hy
  have hinv : ∀ y ∈ kernelTwo S a β, Odd (orderOf y) →
      r * y * r⁻¹ = y⁻¹ → y = 1 := by
    intro y hy hodd hyinv
    have hβmem : aVec S h.mem_Q ∈ commSpace (rhoLin S β) :=
      aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
        h.centerIn_Qa_not_le_Q hβR hβ1
    have hyfix : rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q :=
      ((mem_kernelTwo S a β).mp hy).2 _ hβmem
    have hρeq : rhoLin S y = 1 := by
      refine CFSG.LargeExtraspecial.eq_one_of_conj_eq_inv_of_apply_eq
        (q := qS S) (ρ := rhoLin S y) (β := rhoLin S r) ?_ ?_ ?_ hyfix ?_
      · simpa [rhoLin] using
          TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (rhoBar S y).2
      · rw [show orderOf (rhoLin S y) = orderOf y from by
            simpa [rhoLin] using orderOf_rhoBar S y]
        exact hodd
      · have hconj : rhoLin S (r * y * r⁻¹) = (rhoLin S y)⁻¹ := by
          rw [hyinv]
          exact rhoLin_inv S y
        calc rhoLin S r * rhoLin S y * (rhoLin S r)⁻¹
            = rhoLin S (r * y * r⁻¹) := by simp only [rhoLin_mul, rhoLin_inv]
          _ = (rhoLin S y)⁻¹ := hconj
      · intro v hv
        simpa [rhoLin] using
          rhoBar_sub_mem_span_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa hr hv
    have h1 : rhoBar S y = 1 := Subtype.ext (by simpa [rhoLin] using hρeq)
    exact rhoBar_injective S (by rw [map_one]; exact h1)
  exact CFSG.GroupTheory.commute_of_forall_conj_eq_inv_imp_eq_one hK hr2 htK hinv k hk

theorem aVec_not_mem_iSup_commSpace_kernelTwo_of_data (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {β γ ω : Hbar z} (hβA2 : β ∈ A2set S)
    (hγcomp : γ ∈ ncComp (A2set S) β) (hω : ω = β * γ) (hγω : γ = ω * β * ω⁻¹)
    (hγ3 : orderOf (β * γ) = 3) (hβR : β ∈ Rbar S a) (hβ1 : β ≠ 1) :
    aVec S h.mem_Q ∉ ⨆ k ∈ kernelTwo S a β, commSpace (rhoLin S k) := by
  have hγA2 : γ ∈ A2set S := CFSG.Timmesfeld.ncComp_subset hβA2 hγcomp
  have hle := commSpace_le_fixSpace_of_mem_kernelTwo S a hβA2 hγcomp hω hγω hγ3
  have hωeq : commSpace (rhoLin S ω) = commSpace (rhoLin S β) ⊔ commSpace (rhoLin S γ) :=
    commSpace_rhoLin_eq_sup_of_orderOf_mul_eq_three S hβA2 hγA2 hω hγ3
  have hω3 : (rhoLin S ω) ^ 3 = 1 := by
    have h3ω : orderOf (rhoLin S ω) = 3 := by
      rw [hω, rhoLin_mul]
      simpa [rhoLin, hγ3] using orderOf_rhoBar S (β * γ)
    simpa [h3ω] using pow_orderOf_eq_one (rhoLin S ω)
  have hbot : commSpace (rhoLin S ω) ⊓ fixSpace (rhoLin S ω) = ⊥ :=
    CFSG.LargeExtraspecial.OrthoF2.commSpace_inf_fixSpace_eq_bot_of_pow_three hω3
  have hsup_le : (⨆ k ∈ kernelTwo S a β, commSpace (rhoLin S k)) ≤ fixSpace (rhoLin S ω) := by
    refine iSup_le fun k => iSup_le fun hk => hle k hk
  intro hmem
  have hfix : aVec S h.mem_Q ∈ fixSpace (rhoLin S ω) := hsup_le hmem
  have hcom : aVec S h.mem_Q ∈ commSpace (rhoLin S ω) := by
    rw [hωeq]
    exact Submodule.mem_sup_left (aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj
      h.not_mem_ZQ h.mem_Qa h.centerIn_Qa_not_le_Q hβR hβ1)
  have hzero : aVec S h.mem_Q = 0 := by
    have hmem' : aVec S h.mem_Q ∈ (⊥ : Submodule (ZMod 2) (Additive (QbarOf S))) := by
      rw [← hbot]
      exact Submodule.mem_inf.mpr ⟨hcom, hfix⟩
    simpa using hmem'
  exact aV_ne_zero S h.mem_Q h.not_mem_ZQ hzero

theorem aVec_not_mem_iSup_commSpace_kernelTwo (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {β : Hbar z} (hβR : β ∈ Rbar S a) (hβ1 : β ≠ 1) :
    aVec S h.mem_Q ∉ ⨆ k ∈ kernelTwo S a β, commSpace (rhoLin S k) := by
  have hβA2 : β ∈ A2set S :=
    Tset_subset_A2set S a (h.mem_Tset_of_mem_Rbar hβR hβ1)
  have hD := A2set_isRootInvolutionSet S
  obtain ⟨γ, hγA2, hγ3⟩ := CFSG.Timmesfeld.exists_orderOf_mul_eq_three
    (Y := Hbar z) (D := A2set S) (fun g x hx => conj_mem_A2set S g hx) hD
    (fun d hd e he => orderOf_mul_le_four_of_mem_A2set S hd he)
    (pCore_two_Hbar_eq_bot S) β hβA2
  have hβγne : ¬ Commute β γ := by
    intro hc
    have h2 : (β * γ) ^ 2 = 1 := by
      rw [pow_two]
      calc β * γ * (β * γ) = β * (γ * β) * γ := by group
        _ = β * (β * γ) * γ := by rw [hc.eq]
        _ = (β * β) * (γ * γ) := by group
        _ = 1 := by rw [hD.mul_self_eq_one hβA2, hD.mul_self_eq_one hγA2, one_mul]
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rw [hγ3] at hdvd
    exact absurd hdvd (by norm_num)
  have hγcomp : γ ∈ ncComp (A2set S) β :=
    CFSG.Timmesfeld.mem_ncComp_of_not_commute hβA2 hγA2 hβγne
  let ω : Hbar z := β * γ
  have hω : ω = β * γ := rfl
  have h2 : β * γ * β * γ * β = γ := by
    have h := congrArg (fun t => t * γ) (show (β * γ) ^ 3 = 1 from by
      simpa [hγ3] using pow_orderOf_eq_one (β * γ))
    simpa [pow_three, mul_assoc, hD.mul_self_eq_one hγA2] using h
  have hωinv : (β * γ)⁻¹ = γ * β := by
    rw [mul_inv_rev, hD.inv_eq hγA2, hD.inv_eq hβA2]
  have hγeq : γ = ω * β * ω⁻¹ := by
    rw [hω, hωinv]
    calc γ = β * γ * β * γ * β := h2.symm
      _ = β * γ * β * (γ * β) := by group
  exact aVec_not_mem_iSup_commSpace_kernelTwo_of_data S h hβA2 hγcomp hω hγeq hγ3 hβR hβ1

theorem rhoLin_apply_eq_self_of_mem_kernelTwo_of_odd (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {β : Hbar z} (hβR : β ∈ Rbar S a) (hβ1 : β ≠ 1)
    {r : Hbar z} (hr : r ∈ Rbar S a) {y : Hbar z} (hy : y ∈ kernelTwo S a β)
    (hodd : Odd (orderOf y)) :
    ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v := by
  have hβA2 : β ∈ A2set S :=
    Tset_subset_A2set S a (h.mem_Tset_of_mem_Rbar hβR hβ1)
  intro v hv
  by_cases hr1 : r = 1
  · rw [hr1] at hv
    have hbot1 : commSpace (rhoLin S (1 : Hbar z)) = ⊥ := by
      rw [show rhoLin S (1 : Hbar z) = 1 from by simp [rhoLin]]
      exact CFSG.LargeExtraspecial.OrthoF2.commSpace_one
    rw [hbot1, Submodule.mem_bot] at hv
    rw [hv]
    simp
  · have htype := isTypeA_rhoBar_of_isA2Hbar S
      (isA2Hbar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
        h.centerIn_Qa_not_le_Q r hr hr1)
    have hW : finrank (ZMod 2) (commSpace (rhoLin S r)) = 2 := by
      simpa [rhoLin] using htype.2.2.2.1
    have hyr : y * r = r * y :=
      (commute_of_mem_Rbar_of_mem_kernelTwo S h hβR hβ1 hr hy).symm
    have hcommρ : rhoLin S y * rhoLin S r = rhoLin S r * rhoLin S y := by
      have := congrArg (rhoLin S) hyr
      simpa [rhoLin_mul] using this
    have hyW : ∀ u ∈ commSpace (rhoLin S r), rhoLin S y u ∈ commSpace (rhoLin S r) :=
      fun u hu => CFSG.LargeExtraspecial.AS35ZS.apply_mem_commSpace_of_commute hcommρ hu
    have hoddy : Odd (orderOf (rhoLin S y)) := by
      rw [show orderOf (rhoLin S y) = orderOf y from by
        simpa [rhoLin] using orderOf_rhoBar S y]
      exact hodd
    have hβa : aVec S h.mem_Q ∈ commSpace (rhoLin S β) :=
      aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
        h.centerIn_Qa_not_le_Q hβR hβ1
    have ha : aVec S h.mem_Q ∈ commSpace (rhoLin S r) :=
      aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
        h.centerIn_Qa_not_le_Q hr hr1
    have hfixa : rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q :=
      ((mem_kernelTwo S a β).mp hy).2 _ hβa
    exact CFSG.LinearAlgebra.apply_eq_self_of_odd_of_apply_eq
      (W := commSpace (rhoLin S r)) hW hyW hoddy ha
      (aV_ne_zero S h.mem_Q h.not_mem_ZQ) hfixa v hv

theorem rhoLin_apply_eq_self_of_mem_oddOrderClosure_kernelTwo (S : Setting z E F) {a : G}
    {w : ℕ} (h : Sec3Hyp S a w) {β : Hbar z} (hβR : β ∈ Rbar S a) (hβ1 : β ≠ 1)
    {r : Hbar z} (hr : r ∈ Rbar S a) {y : Hbar z}
    (hy : y ∈ CFSG.GroupTheory.oddOrderClosure (kernelTwo S a β)) :
    ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v := by
  rw [CFSG.GroupTheory.oddOrderClosure_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
      exact rhoLin_apply_eq_self_of_mem_kernelTwo_of_odd S h hβR hβ1 hr hg.1 hg.2
  | one =>
      intro v _
      simp [rhoLin]
  | mul x y hx hy ihx ihy =>
      intro v hv
      rw [rhoLin_mul]
      simp only [LinearEquiv.mul_apply]
      rw [ihy v hv, ihx v hv]
  | inv x hx ihx =>
      intro v hv
      rw [rhoLin_inv]
      have h := congrArg (fun u => (rhoLin S x)⁻¹ u) (ihx v hv)
      simpa using h.symm

theorem kernelTwo_eq_bot (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    {β : Hbar z} (hβR : β ∈ Rbar S a) (hβ1 : β ≠ 1) : kernelTwo S a β = ⊥ := by
  have hβA2 : β ∈ A2set S :=
    Tset_subset_A2set S a (h.mem_Tset_of_mem_Rbar hβR hβ1)
  let Y : Subgroup (Hbar z) := CFSG.GroupTheory.oddOrderClosure (kernelTwo S a β)
  have hYle : Y ≤ kernelTwo S a β := CFSG.GroupTheory.oddOrderClosure_le _
  have hY1 : CFSG.GroupTheory.oddOrderClosure Y = Y :=
    CFSG.GroupTheory.oddOrderClosure_oddOrderClosure (kernelTwo S a β)
  have hY2 : ∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
      Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥ :=
    fun P hP hPg hN => eq_bot_of_le_oddOrderClosure_kernelTwo S a hβA2 P hP hPg hN
  have hY3 : ∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y := by
    intro y hy r hr
    exact (commute_of_mem_Rbar_of_mem_kernelTwo S h hβR hβ1 hr (hYle hy)).symm
  have hY4 : ∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r),
      rhoLin S y v = v := by
    intro y hy r hr
    exact rhoLin_apply_eq_self_of_mem_oddOrderClosure_kernelTwo S h hβR hβ1 hr hy
  have hleK : (⨆ y ∈ Y, commSpace (rhoLin S y)) ≤
      (⨆ k ∈ kernelTwo S a β, commSpace (rhoLin S k)) := by
    refine iSup_le fun y => iSup_le fun hy => ?_
    exact le_iSup₂ (f := fun k (_ : k ∈ kernelTwo S a β) => commSpace (rhoLin S k))
      y (hYle hy)
  have hY5 : aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) :=
    fun hmem => aVec_not_mem_iSup_commSpace_kernelTwo S h hβR hβ1 (hleK hmem)
  have hY6 : Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) := by
    have hLNK : Lbar S a ≤ Subgroup.normalizer (kernelTwo S a β : Set (Hbar z)) := by
      intro l hl
      exact mem_normalizer_kernelTwo_of_commute S a hβA2
        (commute_of_mem_Lbar S h.mem_Q h.isConj hl (Rbar_le_Lbar S a hβR))
    exact hLNK.trans
      (CFSG.GroupTheory.normalizer_le_normalizer_oddOrderClosure (kernelTwo S a β))
  have happ := h217 Y hY1 hY2 hY3 hY4 hY5 hY6
  rcases happ with hR | hYbot
  · exact absurd hR h.Rbar_ne_bot
  · have hYbot' : CFSG.GroupTheory.oddOrderClosure (kernelTwo S a β) = ⊥ := hYbot
    have hK2 : IsPGroup 2 (kernelTwo S a β) := by
      obtain ⟨k, hk⟩ := CFSG.GroupTheory.index_oddOrderClosure_eq_two_pow
        (kernelTwo S a β)
      have hsub : ((CFSG.GroupTheory.oddOrderClosure (kernelTwo S a β)).subgroupOf
          (kernelTwo S a β)) = ⊥ := by
        rw [hYbot']
        exact Subgroup.bot_subgroupOf (H := kernelTwo S a β)
      rw [hsub, Subgroup.index_bot] at hk
      exact IsPGroup.of_card (p := 2) hk
    exact eq_bot_of_le_kernelTwo S a hβA2 (kernelTwo S a β) le_rfl hK2
      (Subgroup.le_normalizer (H := kernelTwo S a β))

end CFSG.RankThree.GF2n.Stroth78
