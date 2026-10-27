module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.RankThree.PartOne.SecRank

open Equiv Equiv.Perm

theorem cycleType_eq_replicate_of_orderOf_two {n : ℕ} {σ : Perm (Fin n)} (h : orderOf σ = 2) :
    σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 := by
  refine Multiset.eq_replicate_card.2 fun m hm => ?_
  have h1 : m ∣ 2 := by
    rw [← h, ← Equiv.Perm.lcm_cycleType]
    exact Multiset.dvd_lcm hm
  have h2 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
  exact (Nat.le_of_dvd (by norm_num) h1).antisymm h2

theorem card_centralizer_involution {n : ℕ} {σ : Perm (Fin n)} (h : orderOf σ = 2) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) =
      Nat.factorial (n - 2 * Multiset.card σ.cycleType) * 2 ^ Multiset.card σ.cycleType *
        Nat.factorial (Multiset.card σ.cycleType) := by
  have hrep := cycleType_eq_replicate_of_orderOf_two h
  set k := Multiset.card σ.cycleType with hk
  have hk0 : k ≠ 0 := by
    intro h0
    have : σ.cycleType = 0 := Multiset.card_eq_zero.1 h0
    have h1 : σ = 1 := Equiv.Perm.cycleType_eq_zero.1 this
    rw [h1, orderOf_one] at h
    omega
  rw [Equiv.Perm.nat_card_centralizer, Fintype.card_fin]
  have hsum : σ.cycleType.sum = 2 * k := by
    rw [hrep]
    simp [Multiset.sum_replicate, hk, mul_comm]
  have hprod : σ.cycleType.prod = 2 ^ k := by
    rw [hrep]
    simp
  have hfin : σ.cycleType.toFinset = {2} := by
    rw [hrep, Multiset.toFinset_replicate]
    simp [hk0]
  have hcount : σ.cycleType.count 2 = k := by
    rw [hrep]
    simp
  rw [hsum, hprod, hfin, Finset.prod_singleton, hcount]

theorem arith_aux : ∀ n < 13, ∀ k < 7, (k = 2 ∨ k = 4 ∨ k = 6) → 2 * k ≤ n →
    ¬ 27 ∣ Nat.factorial (n - 2 * k) * 2 ^ k * Nat.factorial k := by
  decide

theorem not_dvd_card_centralizer_alternating {n : ℕ} (hn : n ≤ 12)
    (t : alternatingGroup (Fin n)) (ht : orderOf t = 2) :
    ¬ 27 ∣ Nat.card (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin n)))) := by
  set σ : Perm (Fin n) := (t : Perm (Fin n)) with hσ
  have hσ2 : orderOf σ = 2 := by rw [hσ, Subgroup.orderOf_coe, ht]
  let f : Subgroup.centralizer ({t} : Set (alternatingGroup (Fin n))) →*
      Subgroup.centralizer ({σ} : Set (Perm (Fin n))) :=
    ((alternatingGroup (Fin n)).subtype.comp
      (Subgroup.centralizer ({t} : Set _)).subtype).codRestrict
      (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) (fun x => by
        have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2
        exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hx))
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun z : Subgroup.centralizer ({σ} : Set (Perm (Fin n))) => (z : Perm (Fin n))) hxy
  intro h27
  have hdvd := (h27.trans (Subgroup.card_dvd_of_injective f hf))
  rw [card_centralizer_involution hσ2] at hdvd
  have hrep := cycleType_eq_replicate_of_orderOf_two hσ2
  set k := Multiset.card σ.cycleType with hk
  have hsum : σ.cycleType.sum = 2 * k := by
    rw [hrep]
    simp [Multiset.sum_replicate, hk, mul_comm]
  have hk0 : k ≠ 0 := by
    intro h0
    have : σ.cycleType = 0 := Multiset.card_eq_zero.1 h0
    have h1 : σ = 1 := Equiv.Perm.cycleType_eq_zero.1 this
    rw [h1, orderOf_one] at hσ2
    omega
  have hsign : Equiv.Perm.sign σ = 1 := (mem_alternatingGroup).1 t.2
  rw [Equiv.Perm.sign_of_cycleType, hsum] at hsign
  have hev : Even (2 * k + k) := (neg_one_pow_eq_one_iff_even (by decide)).1 hsign
  have hsupp : σ.cycleType.sum = σ.support.card := Equiv.Perm.sum_cycleType σ
  have hle : σ.support.card ≤ n := by
    simpa using Finset.card_le_univ σ.support
  have h2k : 2 * k ≤ n := by omega
  obtain ⟨j, hj⟩ := hev
  have hk3 : k = 2 ∨ k = 4 ∨ k = 6 := by omega
  exact arith_aux n (by omega) k (by omega) hk3 h2k hdvd

end CFSG.RankThree.PartOne.SecRank
