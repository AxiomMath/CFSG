module

import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup

private theorem k91ciso_symm_mem_center {K M : Type*} [Group K] [Group M] (ι : K ≃* M) {c : M}
    (hc : c ∈ center M) : ι.symm c ∈ center K := by
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro g
  apply ι.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
  exact hc (ι g)

theorem center_eq_zpowers_of_mulEquiv {K M : Type*} [Group K] [Group M] [Finite K] (ι : K ≃* M)
    {c : M} (hc : c ∈ center M) (hord : orderOf c = Nat.card (center K)) :
    center K = zpowers (ι.symm c) :=
  (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (k91ciso_symm_mem_center ι hc))
    (by rw [Nat.card_zpowers, MulEquiv.orderOf_eq, hord])).symm

theorem mem_zpowers_sq_of_orderOf_eq_three {G : Type*} [Group G] {g x : G} (hg : orderOf g = 6)
    (hx : x ∈ zpowers g) (hx3 : orderOf x = 3) : x ∈ zpowers (g ^ 2) := by
  have hfin : IsOfFinOrder g := orderOf_pos_iff.mp (by omega)
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr hx)
  have h3 : (g ^ n) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (g ^ n)
    rwa [hx3] at this
  rw [← pow_mul] at h3
  have h6 : 6 ∣ n * 3 := by
    have := orderOf_dvd_of_pow_eq_one h3
    rwa [hg] at this
  obtain ⟨m, rfl⟩ : 2 ∣ n := by omega
  rw [pow_mul]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m

private theorem k91ccyc_exists_orderOf {K : Type*} [Group K] [Finite K] {n : ℕ}
    (hn : n = 3 ∨ n = 6) (hZ : Nat.card (center K) = n) : ∃ z ∈ center K, orderOf z = n := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hn with rfl | rfl
  · obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := center K) 3 (by rw [hZ])
    exact ⟨u, u.2, by rw [Subgroup.orderOf_coe, hu]⟩
  · obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := center K) 2 (by rw [hZ]; decide)
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := center K) 3 (by rw [hZ]; decide)
    rw [← Subgroup.orderOf_coe] at hu hv
    refine ⟨(u : K) * v, mul_mem u.2 v.2, ?_⟩
    have hcomm : Commute (u : K) v := Subgroup.mem_center_iff.mp v.2 u
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hu, hv]; decide), hu, hv]

theorem exists_zpowers_eq_center {K : Type*} [Group K] [Finite K] {n : ℕ} (hn : n = 3 ∨ n = 6)
    (hZ : Nat.card (center K) = n) : ∃ z : K, center K = zpowers z := by
  obtain ⟨z, hz, hzo⟩ := k91ccyc_exists_orderOf hn hZ
  exact ⟨z, (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
    (by rw [Nat.card_zpowers, hzo, hZ])).symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
