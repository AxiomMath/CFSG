module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEnd

import CFSG.RankThree.GF2n.Stroth78.Sec3Three
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndPlane

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open Matrix Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

namespace Sec4PSUEnd

private theorem exists_of_mulEquiv_perm_three {C : Type*} [Group C]
    (ψ : C ≃* Equiv.Perm (Fin 3)) :
    ∃ ρ : C, ρ ^ 3 = 1 ∧ ρ ≠ 1 ∧ ∃ r : C, r * r = 1 ∧ ρ * ρ = ρ * r * ρ⁻¹ * r ∧
      ∀ c : C, c ^ 3 = 1 → c = 1 ∨ c = ρ ∨ c = ρ ^ 2 := by
  obtain ⟨τ, σ, hτ3, hτ1, hσσ, hττ, hcl⟩ : ∃ τ σ : Equiv.Perm (Fin 3), τ ^ 3 = 1 ∧ τ ≠ 1 ∧
      σ * σ = 1 ∧ τ * τ = τ * σ * τ⁻¹ * σ ∧
      ∀ g : Equiv.Perm (Fin 3), g ^ 3 = 1 → g = 1 ∨ g = τ ∨ g = τ ^ 2 :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 0 1, by decide, by decide, by decide,
      by decide, by decide⟩
  refine ⟨ψ.symm τ, by rw [← map_pow, hτ3, map_one], fun h1 => hτ1 ?_, ψ.symm σ,
    by rw [← map_mul, hσσ, map_one], by simpa only [map_mul, map_inv] using congrArg ψ.symm hττ,
    fun c hc => ?_⟩
  · simpa using congrArg ψ h1
  · have hc' : (ψ c) ^ 3 = 1 := by rw [← map_pow, hc, map_one]
    rcases hcl _ hc' with h | h | h
    · exact Or.inl (by simpa using congrArg ψ.symm h)
    · exact Or.inr (Or.inl (by simpa using congrArg ψ.symm h))
    · exact Or.inr (Or.inr (by simpa [map_pow] using congrArg ψ.symm h))

theorem odd_card_centralizer_Xsub (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    (hw : w ≤ 5) :
    Odd (Nat.card (Subgroup.centralizer (Xsub S a : Set (Hbar z)))) := by
  classical
  by_contra hodd
  obtain ⟨ψ⟩ := nonempty_mulEquiv_perm_three_centralizer_Xsub S h h217
    (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨ρC, hρ3C, hρ1C, rC, hrrC, hρρC, hclC⟩ := exists_of_mulEquiv_perm_three ψ
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Hbar z, ρ = ρC := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : Hbar z, r = rC := ⟨_, rfl⟩
  have hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) := hρdef ▸ ρC.2
  have hrC : r ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) := hrdef ▸ rC.2
  have hρ3 : ρ ^ 3 = 1 := by
    rw [hρdef]
    exact_mod_cast hρ3C
  have hρ1 : ρ ≠ 1 := by
    rw [hρdef]
    exact_mod_cast hρ1C
  have hrr : r * r = 1 := by
    rw [hrdef]
    exact_mod_cast hrrC
  have hρρ : ρ * ρ = ρ * r * ρ⁻¹ * r := by
    rw [hρdef, hrdef]
    exact_mod_cast hρρC
  have hcl : ∀ c ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)), c ^ 3 = 1 →
      c = 1 ∨ c = ρ ∨ c = ρ ^ 2 := by
    intro c hc hc3
    rcases hclC ⟨c, hc⟩ (Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hc3)) with
      h1 | h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · refine Or.inr (Or.inl ?_)
      rw [hρdef]
      exact congrArg Subtype.val h1
    · refine Or.inr (Or.inr ?_)
      rw [hρdef]
      exact (congrArg Subtype.val h1).trans (SubgroupClass.coe_pow ρC 2)
  have hr'C : ρ * r * ρ⁻¹ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) :=
    mul_mem (mul_mem hρC hrC) (inv_mem hρC)
  have hr'r' : ρ * r * ρ⁻¹ * (ρ * r * ρ⁻¹) = 1 := by
    calc ρ * r * ρ⁻¹ * (ρ * r * ρ⁻¹) = ρ * (r * r) * ρ⁻¹ := by group
      _ = 1 := by rw [hrr, mul_one, mul_inv_cancel]
  have hrho1 : rhoLin S 1 = 1 := by simp [rhoLin]
  have : Finite (Additive (QbarOf S)) := inferInstance
  have : Module.Finite (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hdim := finrank_QbarOf_eq_two_mul S h.card_F
  have hfixT : ∀ t ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)), t * t = 1 →
      ∀ x ∈ Xsub S a, ∀ u ∈ commSpace (rhoLin S t), rhoLin S x u = u := by
    intro t ht htt
    have htt' : rhoLin S t * rhoLin S t = 1 := by rw [← rhoLin_mul, htt, hrho1]
    have h2 := two_mul_finrank_commSpace_le (K := ZMod 2) htt'
    exact rhoLin_eq_self_of_finrank_le_five (U := commSpace (rhoLin S t)) S h h217 h3 hα hpsu
      (fun x hx u hu => rhoLin_mem_commSpace_of_commute S
        (Subgroup.mem_centralizer_iff.mp ht x hx) hu) (by omega)
  have hfixρ : ∀ x ∈ Xsub S a, ∀ v,
      rhoLin S x (rhoLin S (ρ * ρ) v - v) = rhoLin S (ρ * ρ) v - v := by
    intro x hx v
    have hsplit : rhoLin S (ρ * ρ) v - v =
        (rhoLin S (ρ * r * ρ⁻¹) (rhoLin S r v) - rhoLin S r v) + (rhoLin S r v - v) := by
      rw [hρρ, rhoLin_mul, LinearEquiv.mul_apply]
      abel
    rw [hsplit, map_add,
      hfixT _ hr'C hr'r' x hx _ (sub_mem_commSpace (rhoLin S (ρ * r * ρ⁻¹)) (rhoLin S r v)),
      hfixT _ hrC hrr x hx _ (sub_mem_commSpace (rhoLin S r) v)]
  have hCn : (Subgroup.centralizer (Xsub S a : Set (Hbar z))).Normal := inferInstance
  have hRn : (Subgroup.zpowers ρ).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hg3 : (g * ρ * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hρ3, mul_one, mul_inv_cancel]
    rw [← conj_zpow]
    refine zpow_mem ?_ k
    rcases hcl _ (hCn.conj_mem ρ hρC g) hg3 with h1 | h1 | h1 <;> rw [h1]
    · exact one_mem _
    · exact Subgroup.mem_zpowers ρ
    · exact pow_mem (Subgroup.mem_zpowers ρ) 2
  have hLR : Lbar S a ≤ Subgroup.normalizer (Subgroup.zpowers ρ : Set (Hbar z)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hRn]
    exact le_top
  obtain ⟨⟨α₀, hα₀R⟩, hα₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα₀1' : α₀ ≠ 1 := fun h1 => hα₀1 (Subtype.ext h1)
  have hα₀X : α₀ ∈ Xsub S a :=
    subset_Xsub S a (Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα₀R hα₀1'))
  have hρα : ρ * α₀ = α₀ * ρ := (Subgroup.mem_centralizer_iff.mp hρC α₀ hα₀X).symm
  obtain ⟨hsum, -⟩ := aVec_add_rhoLin_add_rhoLin_eq_zero S h h217 hρ3 hρ1 hLR hα₀R hα₀1' hρα
  have hρ4 : ρ * ρ * (ρ * ρ) = ρ := by
    calc ρ * ρ * (ρ * ρ) = ρ * ρ * ρ * ρ := by rw [← mul_assoc]
      _ = ρ ^ 3 * ρ := by rw [pow_three']
      _ = ρ := by rw [hρ3, one_mul]
  have hpqs : aVec S h.mem_Q = rhoLin S (ρ * ρ) (rhoLin S (ρ * ρ) (aVec S h.mem_Q)) -
      rhoLin S (ρ * ρ) (aVec S h.mem_Q) := by
    rw [← LinearEquiv.mul_apply, ← rhoLin_mul, hρ4, sub_eq_add_vec (ZMod 2)]
    rw [add_assoc] at hsum
    exact (eq_neg_of_add_eq_zero_left hsum).trans (neg_vec_eq (ZMod 2) _)
  obtain ⟨x, hx, hxa⟩ := exists_rhoLin_aVec_ne S h h217 h3 hα hpsu
  exact hxa (by rw [hpqs]; exact hfixρ x hx _)

end Sec4PSUEnd

end CFSG.RankThree.GF2n.Stroth78
