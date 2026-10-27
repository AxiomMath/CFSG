module

public import CFSG.RankThree.GF2n.Stroth78.Sec3LbarBound

import CFSG.RankThree.GF2n.Stroth78.Sec2Five
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
import CFSG.LinearAlgebra.F2PlaneMaps
import CFSG.LargeExtraspecial.OrthoF2Inverted
import CFSG.LargeExtraspecial.OrthoF2PairsCases

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem exists_apply_ne_commSpace_of_mem_closure_Eset_diff (S : Setting z E F) {a : G}
    {β : Hbar z} (hK : kernelTwo S a β = ⊥) {x : Hbar z}
    (hx : x ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β)) (hx3 : orderOf x = 3) :
    ∃ u ∈ commSpace (rhoLin S β), rhoLin S x u ≠ u := by
  by_contra hc
  push Not at hc
  have hker : x ∈ kernelTwo S a β := (mem_kernelTwo S a β).mpr ⟨hx, hc⟩
  rw [hK] at hker
  have h1 : x = 1 := by simpa using hker
  rw [h1, orderOf_one] at hx3
  norm_num at hx3

theorem finrank_commSpace_rhoLin_eq_two (S : Setting z E F) {β : Hbar z}
    (hβ : β ∈ A2set S) : finrank (ZMod 2) (commSpace (rhoLin S β)) = 2 := by
  simpa [rhoLin] using (isTypeA_rhoBar_of_isA2Hbar S hβ).2.2.2.1

theorem exists_mem_Eset_orderOf_mul_eq_three (S : Setting z E F) (a : G) {γ : Hbar z}
    (hγ : γ ∈ Eset S a) : ∃ c ∈ Eset S a, orderOf (γ * c) = 3 := by
  have hD : CFSG.Timmesfeld.IsRootInvolutionSet (A2set S) := A2set_isRootInvolutionSet S
  have hN : ∀ g x : Hbar z, x ∈ A2set S → g * x * g⁻¹ ∈ A2set S :=
    fun g x hx => conj_mem_A2set S g hx
  have h4 : ∀ d ∈ A2set S, ∀ e ∈ A2set S, orderOf (d * e) ≤ 4 :=
    fun d hd e he => orderOf_mul_le_four_of_mem_A2set S hd he
  have hγD : γ ∈ A2set S := Eset_subset_A2set S a hγ
  obtain ⟨c, hcD, h3⟩ :=
    CFSG.Timmesfeld.exists_orderOf_mul_eq_three hN hD h4 (pCore_two_Hbar_eq_bot S) γ hγD
  have hnc : ¬ Commute γ c := by
    intro hcomm
    have h2 := hcomm.orderOf_mul_dvd_lcm
    rw [orderOf_eq_two_of_mem_A2set S hγD, orderOf_eq_two_of_mem_A2set S hcD] at h2
    norm_num at h2
    rw [h3] at h2
    norm_num at h2
  have hcγ : c ∈ ncComp (A2set S) γ := mem_ncComp_of_not_commute hγD hcD hnc
  exact ⟨c, ncComp_subset_of_invariant hN hD h4 (pCore_two_Hbar_eq_bot S)
    (Eset_subset_A2set S a) (fun g x hx => Eset_conj_mem S a hx g) hγ hcγ, h3⟩

theorem exists_mul_orderOf_eq_three_of_mem_Eset_diff (S : Setting z E F) (a : G) {β γ : Hbar z}
    (hγ : γ ∈ Eset S a \ ncComp (A2set S) β) :
    ∃ c ∈ Eset S a \ ncComp (A2set S) β, orderOf (γ * c) = 3 := by
  obtain ⟨c, hcE, h3⟩ := exists_mem_Eset_orderOf_mul_eq_three S a hγ.1
  have hγD : γ ∈ A2set S := Eset_subset_A2set S a hγ.1
  have hcD : c ∈ A2set S := Eset_subset_A2set S a hcE
  have hnc : ¬ Commute γ c := by
    intro hcomm
    have h2 := hcomm.orderOf_mul_dvd_lcm
    rw [orderOf_eq_two_of_mem_A2set S hγD, orderOf_eq_two_of_mem_A2set S hcD] at h2
    norm_num at h2
    rw [h3] at h2
    norm_num at h2
  have hcγ : c ∈ ncComp (A2set S) γ := mem_ncComp_of_not_commute hγD hcD hnc
  refine ⟨c, ⟨hcE, ?_⟩, h3⟩
  intro hcβ
  have heq : ncComp (A2set S) c = ncComp (A2set S) β := ncComp_eq_of_mem hcβ
  exact hγ.2 (by rw [← heq]; exact mem_ncComp_symm hcγ)

theorem aVec_mem_commSpace_of_mem_closure_Eset_diff (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {β : Hbar z} (hβR : β ∈ Rbar S a) (hβ1 : β ≠ 1)
    (hK : kernelTwo S a β = ⊥) {ω : Hbar z}
    (hω : ω ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β)) (hω3 : orderOf ω = 3) :
    aVec S h.mem_Q ∈ commSpace (rhoLin S ω) := by
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hβA2 : β ∈ A2set S := Tset_subset_A2set S a (h.mem_Tset_of_mem_Rbar hβR hβ1)
  have hWdim : finrank (ZMod 2) (commSpace (rhoLin S β)) = 2 :=
    finrank_commSpace_rhoLin_eq_two S hβA2
  have hωW : ∀ u ∈ commSpace (rhoLin S β), rhoLin S ω u ∈ commSpace (rhoLin S β) :=
    fun u hu => rhoBar_mem_commSpace_of_mem_closure_Eset_diff S a hβA2 hω hu
  have hne : ∃ u ∈ commSpace (rhoLin S β), rhoLin S ω u ≠ u :=
    exists_apply_ne_commSpace_of_mem_closure_Eset_diff S hK hω hω3
  have hfree : commSpace (rhoLin S β) ⊓ fixSpace (rhoLin S ω) = ⊥ :=
    CFSG.LinearAlgebra.inf_fixSpace_eq_bot_of_pow_three hWdim hωW
      (rhoLin_pow_three_eq_one S hω3) hne
  have hle : commSpace (rhoLin S β) ≤ commSpace (rhoLin S ω) :=
    CFSG.LargeExtraspecial.le_commSpace_of_inf_fixSpace_eq_bot hωW hfree
  have haW : aVec S h.mem_Q ∈ commSpace (rhoLin S β) :=
    aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
      h.centerIn_Qa_not_le_Q hβR hβ1
  exact hle haW

theorem eq_of_apply_eq_on_commSpace (S : Setting z E F) {a : G} {β : Hbar z}
    (hK : kernelTwo S a β = ⊥) {ω y : Hbar z}
    (hω : ω ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β))
    (hy : y ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β))
    (hcase : ∀ u ∈ commSpace (rhoLin S β), rhoLin S y u = rhoLin S ω u) :
    y = ω := by
  have hkmem : ω⁻¹ * y ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hω) hy
  have hker : ω⁻¹ * y ∈ kernelTwo S a β := by
    refine (mem_kernelTwo S a β).mpr ⟨hkmem, ?_⟩
    intro u hu
    rw [rhoLin_mul, rhoLin_inv, LinearEquiv.mul_apply, hcase u hu]
    simp
  have h1 : ω⁻¹ * y = 1 := by
    rw [hK] at hker
    simpa using hker
  calc y = ω * (ω⁻¹ * y) := by group
    _ = ω := by rw [h1, mul_one]

theorem eq_inv_of_apply_eq_sq_on_commSpace (S : Setting z E F) {a : G} {β : Hbar z}
    (hK : kernelTwo S a β = ⊥) {ω y : Hbar z}
    (hω : ω ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β))
    (hy : y ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β))
    (hω3 : orderOf ω = 3)
    (hcase : ∀ u ∈ commSpace (rhoLin S β), rhoLin S y u = rhoLin S ω (rhoLin S ω u)) :
    y = ω⁻¹ := by
  have hkmem : ω⁻¹ * ω⁻¹ * y ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hω) (Subgroup.inv_mem _ hω)) hy
  have hker : ω⁻¹ * ω⁻¹ * y ∈ kernelTwo S a β := by
    refine (mem_kernelTwo S a β).mpr ⟨hkmem, ?_⟩
    intro u hu
    rw [rhoLin_mul, rhoLin_mul, rhoLin_inv, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, hcase u hu]
    simp
  have h1 : ω⁻¹ * ω⁻¹ * y = 1 := by
    rw [hK] at hker
    simpa using hker
  have hsq : ω ^ 2 = ω⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc ω ^ 2 * ω = ω ^ 3 := by
          rw [show ω ^ 3 = ω ^ 2 * ω from pow_succ ω 2]
      _ = 1 := by rw [← hω3]; exact pow_orderOf_eq_one ω
  calc y = (ω * ω) * (ω⁻¹ * ω⁻¹ * y) := by group
    _ = ω * ω := by rw [h1, mul_one]
    _ = ω ^ 2 := (pow_two ω).symm
    _ = ω⁻¹ := hsq

theorem conj_eq_or_eq_inv_of_mem_Lbar (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {β : Hbar z} (hβR : β ∈ Rbar S a) (hβ1 : β ≠ 1)
    (hK : kernelTwo S a β = ⊥) {ω : Hbar z}
    (hω : ω ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β)) (hω3 : orderOf ω = 3)
    {ℓ : Hbar z} (hℓ : ℓ ∈ Lbar S a) :
    ℓ * ω * ℓ⁻¹ = ω ∨ ℓ * ω * ℓ⁻¹ = ω⁻¹ := by
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hβA2 : β ∈ A2set S := Tset_subset_A2set S a (h.mem_Tset_of_mem_Rbar hβR hβ1)
  have hℓβ : ℓ * β = β * ℓ :=
    commute_of_mem_Lbar S h.mem_Q h.isConj hℓ (Rbar_le_Lbar S a hβR)
  have hω' : ℓ * ω * ℓ⁻¹ ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β) :=
    conj_mem_closure_Eset_diff_ncComp S a hℓβ hω
  have hWdim : finrank (ZMod 2) (commSpace (rhoLin S β)) = 2 :=
    finrank_commSpace_rhoLin_eq_two S hβA2
  have hxW : ∀ u ∈ commSpace (rhoLin S β), rhoLin S ω u ∈ commSpace (rhoLin S β) :=
    fun u hu => rhoBar_mem_commSpace_of_mem_closure_Eset_diff S a hβA2 hω hu
  have hyW : ∀ u ∈ commSpace (rhoLin S β),
      rhoLin S (ℓ * ω * ℓ⁻¹) u ∈ commSpace (rhoLin S β) :=
    fun u hu => rhoBar_mem_commSpace_of_mem_closure_Eset_diff S a hβA2 hω' hu
  have hx3 : (rhoLin S ω) ^ 3 = 1 := rhoLin_pow_three_eq_one S hω3
  have hy3 : (rhoLin S (ℓ * ω * ℓ⁻¹)) ^ 3 = 1 := by
    rw [rhoLin_conj]
    calc (rhoLin S ℓ * rhoLin S ω * (rhoLin S ℓ)⁻¹) ^ 3
        = rhoLin S ℓ * (rhoLin S ω) ^ 3 * (rhoLin S ℓ)⁻¹ := conj_pow
      _ = 1 := by rw [hx3, mul_one, mul_inv_cancel]
  have hx : ∃ u ∈ commSpace (rhoLin S β), rhoLin S ω u ≠ u :=
    exists_apply_ne_commSpace_of_mem_closure_Eset_diff S hK hω hω3
  have hord : orderOf (ℓ * ω * ℓ⁻¹) = 3 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj ℓ) ω
    rw [MulAut.conj_apply] at h
    rw [h, hω3]
  have hy : ∃ u ∈ commSpace (rhoLin S β), rhoLin S (ℓ * ω * ℓ⁻¹) u ≠ u :=
    exists_apply_ne_commSpace_of_mem_closure_Eset_diff S hK hω' hord
  rcases CFSG.LinearAlgebra.forall_apply_eq_or_forall_apply_eq_sq hWdim hxW hyW hx3 hy3 hx hy
    with hcase | hcase
  · left
    exact eq_of_apply_eq_on_commSpace S hK hω hω' hcase
  · right
    exact eq_inv_of_apply_eq_sq_on_commSpace S hK hω hω' hω3 hcase

theorem card_Lbar_le_four_of_mem_Eset_diff (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {β : Hbar z} (hβR : β ∈ Rbar S a) (hβ1 : β ≠ 1)
    (hK : kernelTwo S a β = ⊥) {γ c : Hbar z}
    (hγ : γ ∈ Eset S a \ ncComp (A2set S) β) (hc : c ∈ Eset S a \ ncComp (A2set S) β)
    (h3 : orderOf (γ * c) = 3) : Nat.card (Lbar S a) ≤ 4 := by
  have hγA2 : γ ∈ A2set S := Eset_subset_A2set S a hγ.1
  have hcA2 : c ∈ A2set S := Eset_subset_A2set S a hc.1
  have htypeγ : CFSG.LargeExtraspecial.IsTypeA (qS S) (rhoLin S γ) 2 :=
    isTypeA_rhoBar_of_isA2Hbar S hγA2
  have htypec : CFSG.LargeExtraspecial.IsTypeA (qS S) (rhoLin S c) 2 :=
    isTypeA_rhoBar_of_isA2Hbar S hcA2
  have h3lin : orderOf (rhoLin S γ * rhoLin S c) = 3 := by
    rw [← rhoLin_mul, orderOf_rhoLin, h3]
  have h4 : finrank (ZMod 2) (commSpace (rhoLin S (γ * c))) = 4 := by
    have h := (CFSG.LargeExtraspecial.commSpace_mul_of_orderOf_eq_three
      (q := qS S) (hq := by letI := modAbF S; exact q_nondegenerate S) htypeγ htypec h3lin).2.2.1
    rw [rhoLin_mul]
    exact h
  have hωmem : γ * c ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure hγ) (Subgroup.subset_closure hc)
  have haω : aVec S h.mem_Q ∈ commSpace (rhoLin S (γ * c)) :=
    aVec_mem_commSpace_of_mem_closure_Eset_diff S h hβR hβ1 hK hωmem h3
  exact card_Lbar_le_four_of_normalizes S h h3 h4 haω
    (fun ℓ hℓ => conj_eq_or_eq_inv_of_mem_Lbar S h hβR hβ1 hK hωmem h3 hℓ)

theorem Eset_subset_ncComp_of_kernelTwo_eq_bot (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {β : Hbar z} (hβR : β ∈ Rbar S a) (hβ1 : β ≠ 1)
    (hK : kernelTwo S a β = ⊥) : Eset S a ⊆ ncComp (A2set S) β := by
  intro γ hγ
  by_contra hγ1
  have hγ' : γ ∈ Eset S a \ ncComp (A2set S) β := ⟨hγ, hγ1⟩
  obtain ⟨c, hc, h3⟩ := exists_mul_orderOf_eq_three_of_mem_Eset_diff S a hγ'
  have hle := card_Lbar_le_four_of_mem_Eset_diff S h hβR hβ1 hK hγ' hc h3
  exact (not_le_of_gt h.four_lt_card_Lbar) hle

theorem Eset_isRootInvolutionSet (S : Setting z E F) (a : G) :
    CFSG.Timmesfeld.IsRootInvolutionSet (Eset S a) := by
  refine CFSG.Timmesfeld.isRootInvolutionSet_of_subset (A2set_isRootInvolutionSet S)
    (Eset_subset_A2set S a) ?_
  intro α hα α' hα' h4
  exact sq_mul_mem_of_invariant
    (fun g x hx => conj_mem_A2set S g hx) (A2set_isRootInvolutionSet S)
    (fun d hd e he => orderOf_mul_le_four_of_mem_A2set S hd he) (pCore_two_Hbar_eq_bot S)
    (Eset_subset_A2set S a) (fun g x hx => Eset_conj_mem S a hx g) hα hα' h4

theorem orderOf_mul_le_four_of_mem_Eset (S : Setting z E F) (a : G) {α α' : Hbar z}
    (hα : α ∈ Eset S a) (hα' : α' ∈ Eset S a) : orderOf (α * α') ≤ 4 :=
  orderOf_mul_le_four_of_mem_A2set S (Eset_subset_A2set S a hα) (Eset_subset_A2set S a hα')

theorem stroth78_31_of_kernelTwo_eq_bot (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {β : Hbar z} (hβR : β ∈ Rbar S a) (hβ1 : β ≠ 1)
    (hK : kernelTwo S a β = ⊥) :
    (Eset S a).Nonempty ∧ CFSG.Timmesfeld.IsRootInvolutionSet (Eset S a) ∧
      (∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 4) ∧
      ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, ∃ x ∈ Xsub S a, α' = x * α * x⁻¹ := by
  refine ⟨?_, Eset_isRootInvolutionSet S a, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := h.Tset_nonempty
    exact ⟨t, Tset_subset_Eset S a ht⟩
  · exact fun α hα α' hα' => orderOf_mul_le_four_of_mem_Eset S a hα hα'
  · have hD : CFSG.Timmesfeld.IsRootInvolutionSet (A2set S) := A2set_isRootInvolutionSet S
    have hN : ∀ g x : Hbar z, x ∈ A2set S → g * x * g⁻¹ ∈ A2set S :=
      fun g x hx => conj_mem_A2set S g hx
    have h4 : ∀ d ∈ A2set S, ∀ e ∈ A2set S, orderOf (d * e) ≤ 4 :=
      fun d hd e he => orderOf_mul_le_four_of_mem_A2set S hd he
    have hβE : β ∈ Eset S a :=
      Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hβR hβ1)
    exact exists_conj_of_subset_ncComp hN hD h4 (pCore_two_Hbar_eq_bot S)
      (Eset_subset_A2set S a) (fun g x hx => Eset_conj_mem S a hx g) hβE
      (Eset_subset_ncComp_of_kernelTwo_eq_bot S h hβR hβ1 hK)

end CFSG.RankThree.GF2n.Stroth78
