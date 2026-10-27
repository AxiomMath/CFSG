module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.SpecificGroups.Alternating

import Mathlib.Tactic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace CFSG
end CFSG
open CFSG

/-! # Odd-order subgroups of `A₇`

Every odd-order subgroup of the alternating group on seven letters has order
at most `21` (source: refs/bender-dihedral-sylow.tex L645–792).
-/

set_option linter.unnecessarySimpa false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

namespace CFSG.GorensteinWalter

private lemma exists_sylow_of_order_prime_pow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {x : G} {n : ℕ} (_hn : 1 ≤ n) (hx : orderOf x = p ^ n) :
    ∃ P : Sylow p G, x ∈ (P : Subgroup G) := by
  let Z : Subgroup G := Subgroup.zpowers x
  have hZp : IsPGroup p Z := by
    apply IsPGroup.of_card (n := n)
    rw [Nat.card_zpowers, hx]
  obtain ⟨P, hZP⟩ := IsPGroup.exists_le_sylow (p := p) hZp
  exact ⟨P, hZP (Subgroup.mem_zpowers x)⟩

private lemma card_prime_power_order_le_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [Fintype (Sylow p G)]
    (A : Set G) (hA : ∀ x : G, x ∈ A ↔ x ≠ 1 ∧ ∃ n : ℕ, 1 ≤ n ∧ orderOf x = p ^ n) :
    Nat.card {x : G // x ∈ A} ≤
      ∑ P : Sylow p G, (Nat.card (P : Subgroup G) - 1) := by
  classical
  let α := Σ P : Sylow p G, {x : ↥(P : Subgroup G) // x ≠ 1}
  let f : α → {x : G // x ∈ A} := fun q =>
    ⟨(q.2 : G), (hA _).mpr
      ⟨(by intro hx; exact q.2.2 (Subtype.ext hx)),
       (by
          have hPp : IsPGroup p (q.1 : Subgroup G) := q.1.isPGroup'
          obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hPp) q.2
          have hkG : orderOf (q.2 : G) = p ^ k := by
            simpa [Subgroup.orderOf_coe] using hk
          have hk1 : 1 ≤ k := by
            by_contra hk0
            have hk0' : k = 0 := by omega
            have hx1 : orderOf (q.2 : G) = 1 := by simpa [hk0'] using hkG
            apply q.2.2
            apply Subtype.ext
            exact orderOf_eq_one_iff.mp hx1
          exact ⟨k, hk1, hkG⟩)⟩⟩
  have hsurj : Function.Surjective f := by
    intro y
    rcases (hA y.1).1 y.2 with ⟨hyne, n, hn, hyord⟩
    obtain ⟨P, hyP⟩ := exists_sylow_of_order_prime_pow (p := p) hn hyord
    refine ⟨⟨P, ⟨⟨y.1, hyP⟩, ?_⟩⟩, ?_⟩
    · intro hzero
      apply hyne
      exact congrArg Subtype.val hzero
    · rfl
  have hleA : Nat.card {x : G // x ∈ A} ≤ Nat.card α :=
    Nat.card_le_card_of_surjective f hsurj
  have hα : Nat.card α = ∑ P : Sylow p G,
      Nat.card {x : ↥(P : Subgroup G) // x ≠ 1} := Nat.card_sigma
  have hpair (P : Sylow p G) :
      Nat.card {x : ↥(P : Subgroup G) // x ≠ 1} = Nat.card (P : Subgroup G) - 1 := by
    letI : Fintype (P : Subgroup G) := Fintype.ofFinite _
    letI : Fintype {x : ↥(P : Subgroup G) // x ≠ 1} := Fintype.ofFinite _
    letI : Fintype {x : ↥(P : Subgroup G) // x = 1} := Fintype.ofFinite _
    have h1 : Fintype.card {x : ↥(P : Subgroup G) // x = 1} = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨1, rfl⟩, ?_⟩
      intro x
      apply Subtype.ext
      simpa using x.2
    have hsplit := Fintype.card_subtype_compl (α := ↥(P : Subgroup G))
      (p := fun x : ↥(P : Subgroup G) => x = 1)
    rw [h1] at hsplit
    rw [Nat.card_eq_fintype_card]
    simpa using hsplit.symm
  calc
    Nat.card {x : G // x ∈ A} ≤ Nat.card α := hleA
    _ = ∑ P : Sylow p G, Nat.card {x : ↥(P : Subgroup G) // x ≠ 1} := hα
    _ = ∑ P : Sylow p G, (Nat.card (P : Subgroup G) - 1) := by simp [hpair]

private lemma card_nonone_le_sum_powers
    {G : Type*} [Group G] [Finite G]
    [Fintype (Sylow 3 G)] [Fintype (Sylow 5 G)] [Fintype (Sylow 7 G)]
    (hall : ∀ x : G, x ≠ 1 →
      (∃ n : ℕ, 1 ≤ n ∧ orderOf x = 3 ^ n) ∨
      (∃ n : ℕ, 1 ≤ n ∧ orderOf x = 5 ^ n) ∨
      (∃ n : ℕ, 1 ≤ n ∧ orderOf x = 7 ^ n)) :
    Nat.card G ≤ 1 +
      (∑ P : Sylow 3 G, (Nat.card (P : Subgroup G) - 1)) +
      (∑ P : Sylow 5 G, (Nat.card (P : Subgroup G) - 1)) +
      (∑ P : Sylow 7 G, (Nat.card (P : Subgroup G) - 1)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let S : Finset G := Finset.univ.filter (fun x : G => x ≠ 1)
  let A : Finset G := S.filter (fun x : G => ∃ n : ℕ, 1 ≤ n ∧ orderOf x = 3 ^ n)
  let B : Finset G := S.filter (fun x : G => ∃ n : ℕ, 1 ≤ n ∧ orderOf x = 5 ^ n)
  let C : Finset G := S.filter (fun x : G => ∃ n : ℕ, 1 ≤ n ∧ orderOf x = 7 ^ n)
  have hcover : S ⊆ A ∪ B ∪ C := by
    intro x hx
    have hxne : x ≠ 1 := by simpa [S] using hx
    rcases hall x hxne with h3 | h5 | h7
    · exact Finset.mem_union_left C (Finset.mem_union_left B (show x ∈ A from by simpa [A, S, hx] using h3))
    · exact Finset.mem_union_left C (Finset.mem_union_right A (show x ∈ B from by simpa [B, S, hx] using h5))
    · exact Finset.mem_union_right (A ∪ B) (show x ∈ C from by simpa [C, S, hx] using h7)
  have hSC : S.card ≤ (A ∪ B ∪ C).card := Finset.card_le_card hcover
  have hunion : (A ∪ B ∪ C).card ≤ A.card + B.card + C.card := by
    have h1 : ((A ∪ B) ∪ C).card ≤ (A ∪ B).card + C.card := Finset.card_union_le (A ∪ B) C
    have h2 : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
    omega
  have hcardG : Nat.card G = 1 + S.card := by
    rw [Nat.card_eq_fintype_card]
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
      (p := fun x : G => x ≠ 1)
    have hone : (Finset.univ.filter fun x : G => x = 1).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨1, ?_⟩
      ext x
      simp
    have hnot : (Finset.univ.filter fun x : G => ¬ x ≠ 1) =
        (Finset.univ.filter fun x : G => x = 1) := by
      ext x
      simp
    rw [hnot, hone] at hsplit
    change Finset.univ.card = 1 + S.card
    rw [show S.card = (Finset.univ.filter fun x : G => x ≠ 1).card by rfl]
    rw [← hsplit, Nat.add_comm]
  have hA3 : A.card ≤ ∑ P : Sylow 3 G, (Nat.card (P : Subgroup G) - 1) := by
    have h := card_prime_power_order_le_sylow (G := G) (p := 3)
      {x : G | x ≠ 1 ∧ ∃ n : ℕ, 1 ≤ n ∧ orderOf x = 3 ^ n} (by intro x; simp)
    have hcard : A.card = Nat.card {x : G // x ∈
        ({x : G | x ≠ 1 ∧ ∃ n : ℕ, 1 ≤ n ∧ orderOf x = 3 ^ n} : Set G)} := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_of_subtype A (by intro x; simp [A, S])).symm
    rw [hcard]
    exact h
  have hB5 : B.card ≤ ∑ P : Sylow 5 G, (Nat.card (P : Subgroup G) - 1) := by
    have h := card_prime_power_order_le_sylow (G := G) (p := 5)
      {x : G | x ≠ 1 ∧ ∃ n : ℕ, 1 ≤ n ∧ orderOf x = 5 ^ n} (by intro x; simp)
    have hcard : B.card = Nat.card {x : G // x ∈
        ({x : G | x ≠ 1 ∧ ∃ n : ℕ, 1 ≤ n ∧ orderOf x = 5 ^ n} : Set G)} := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_of_subtype B (by intro x; simp [B, S])).symm
    rw [hcard]
    exact h
  have hC7 : C.card ≤ ∑ P : Sylow 7 G, (Nat.card (P : Subgroup G) - 1) := by
    have h := card_prime_power_order_le_sylow (G := G) (p := 7)
      {x : G | x ≠ 1 ∧ ∃ n : ℕ, 1 ≤ n ∧ orderOf x = 7 ^ n} (by intro x; simp)
    have hcard : C.card = Nat.card {x : G // x ∈
        ({x : G | x ≠ 1 ∧ ∃ n : ℕ, 1 ≤ n ∧ orderOf x = 7 ^ n} : Set G)} := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_of_subtype C (by intro x; simp [C, S])).symm
    rw [hcard]
    exact h
  let s3 : ℕ := ∑ P : Sylow 3 G, (Nat.card (P : Subgroup G) - 1)
  let s5 : ℕ := ∑ P : Sylow 5 G, (Nat.card (P : Subgroup G) - 1)
  let s7 : ℕ := ∑ P : Sylow 7 G, (Nat.card (P : Subgroup G) - 1)
  have hcomb : A.card + B.card + C.card ≤ s3 + s5 + s7 := by
    dsimp [s3, s5, s7] at hA3 hB5 hC7 ⊢
    omega
  have h1 : Nat.card G ≤ 1 + (A.card + B.card + C.card) := by
    rw [hcardG]
    omega
  have h2 : 1 + (A.card + B.card + C.card) ≤ 1 + (s3 + s5 + s7) := by
    omega
  have hfin_eq : 1 + (s3 + s5 + s7) =
      1 + (∑ P : Sylow 3 G, (Nat.card (P : Subgroup G) - 1)) +
        (∑ P : Sylow 5 G, (Nat.card (P : Subgroup G) - 1)) +
        (∑ P : Sylow 7 G, (Nat.card (P : Subgroup G) - 1)) := by
    dsimp [s3, s5, s7]
    omega
  exact h1.trans (h2.trans hfin_eq.le)

private lemma orderOf_perm_fin_seven_dvd_420 (σ : Equiv.Perm (Fin 7)) :
    orderOf σ ∣ 420 := by
  rw [← Equiv.Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro n hn
  have hn2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
  have hn7 : n ≤ 7 := by
    exact (Equiv.Perm.le_card_support_of_mem_cycleType hn).trans
      (by simpa using Finset.card_le_univ σ.support)
  interval_cases n <;> norm_num

private lemma exists_mem_dvd_of_prime_dvd_lcm {s : Multiset ℕ} {p : ℕ}
    (hp : p.Prime) (h : p ∣ s.lcm) : ∃ n : ℕ, n ∈ s ∧ p ∣ n := by
  induction s using Multiset.induction_on with
  | empty =>
      exact False.elim (hp.not_dvd_one (by simpa using h))
  | cons a s ih =>
      rw [Multiset.lcm_cons] at h
      simp only [lcm_eq_nat_lcm] at h
      rw [Nat.Prime.dvd_lcm hp] at h
      rcases h with ha | hs
      · exact ⟨a, by simp, ha⟩
      · rcases ih hs with ⟨n, hn, hpdvd⟩
        exact ⟨n, by simp [hn], hpdvd⟩

private lemma exists_cycle_length_dvd_of_prime_dvd_order
    (σ : Equiv.Perm (Fin 7)) {p : ℕ} (hp : p.Prime)
    (h : p ∣ orderOf σ) :
    ∃ n : ℕ, n ∈ σ.cycleType ∧ p ∣ n := by
  exact exists_mem_dvd_of_prime_dvd_lcm hp (by simpa [Equiv.Perm.lcm_cycleType] using h)

private lemma cycle_length_le_seven (σ : Equiv.Perm (Fin 7)) {n : ℕ}
    (hn : n ∈ σ.cycleType) : n ≤ 7 := by
  exact (Equiv.Perm.le_card_support_of_mem_cycleType hn).trans
    (by simpa using Finset.card_le_univ σ.support)

private lemma two_mem_sum_ge {s : Multiset ℕ} {a b : ℕ}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : a + b ≤ s.sum := by
  rcases s.exists_cons_of_mem ha with ⟨t, rfl⟩
  rw [Multiset.sum_cons]
  have hbt : b ∈ t := by
    exact (Multiset.mem_cons.mp hb).resolve_left (by exact fun hba => hab hba.symm)
  have hle : b ≤ t.sum := Multiset.le_sum_of_mem hbt
  omega

private lemma three_mem_sum_ge {s : Multiset ℕ} {a b c : ℕ}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : a + b + c ≤ s.sum := by
  rcases s.exists_cons_of_mem ha with ⟨t, rfl⟩
  rw [Multiset.sum_cons]
  have hbt : b ∈ t := (Multiset.mem_cons.mp hb).resolve_left (by exact fun hba => hab hba.symm)
  have hct : c ∈ t := (Multiset.mem_cons.mp hc).resolve_left (by exact fun hca => hac hca.symm)
  have hsum : b + c ≤ t.sum := two_mem_sum_ge hbt hct hbc
  omega

private lemma no_order_15 (x : alternatingGroup (Fin 7)) : orderOf x ≠ 15 := by
  intro h
  let σ : Equiv.Perm (Fin 7) := (x : Equiv.Perm (Fin 7))
  have hσ15 : orderOf σ = 15 := by simpa [σ, Subgroup.orderOf_coe] using h
  have h3 : 3 ∣ orderOf σ := by rw [hσ15]; norm_num
  have h5 : 5 ∣ orderOf σ := by rw [hσ15]; norm_num
  obtain ⟨n3, hn3, h3n⟩ := exists_cycle_length_dvd_of_prime_dvd_order σ Nat.prime_three h3
  obtain ⟨n5, hn5, h5n⟩ := exists_cycle_length_dvd_of_prime_dvd_order σ Nat.prime_five h5
  have hn3ge : 3 ≤ n3 := Nat.le_of_dvd (by have h2 := Equiv.Perm.two_le_of_mem_cycleType hn3; omega) h3n
  have hn5ge : 5 ≤ n5 := Nat.le_of_dvd (by have h2 := Equiv.Perm.two_le_of_mem_cycleType hn5; omega) h5n
  have hle3 : n3 ≤ 7 := cycle_length_le_seven σ hn3
  have hne : n3 ≠ n5 := by
    intro hEq
    have h5n3 : 5 ∣ n3 := by simpa [hEq] using h5n
    have hcop : Nat.Coprime 3 5 := by norm_num
    have h15 : 15 ∣ n3 := by
      rw [show (15 : ℕ) = 3 * 5 by norm_num]
      exact hcop.mul_dvd_of_dvd_of_dvd h3n h5n3
    have hn3pos : 0 < n3 := by have h2 := Equiv.Perm.two_le_of_mem_cycleType hn3; omega
    have h15le : 15 ≤ n3 := Nat.le_of_dvd hn3pos h15
    omega
  have hsum := two_mem_sum_ge hn3 hn5 hne
  have hsumle : σ.cycleType.sum ≤ 7 := by
    simpa [Equiv.Perm.sum_cycleType] using Finset.card_le_univ σ.support
  have : 8 ≤ 7 := by omega
  omega

private lemma no_order_21 (x : alternatingGroup (Fin 7)) : orderOf x ≠ 21 := by
  intro h
  let σ : Equiv.Perm (Fin 7) := (x : Equiv.Perm (Fin 7))
  have hσ21 : orderOf σ = 21 := by simpa [σ, Subgroup.orderOf_coe] using h
  have h3 : 3 ∣ orderOf σ := by rw [hσ21]; norm_num
  have h7 : 7 ∣ orderOf σ := by rw [hσ21]; norm_num
  obtain ⟨n3, hn3, h3n⟩ := exists_cycle_length_dvd_of_prime_dvd_order σ Nat.prime_three h3
  obtain ⟨n7, hn7, h7n⟩ := exists_cycle_length_dvd_of_prime_dvd_order σ Nat.prime_seven h7
  have hn3ge : 3 ≤ n3 := Nat.le_of_dvd (by have h2 := Equiv.Perm.two_le_of_mem_cycleType hn3; omega) h3n
  have hn7ge : 7 ≤ n7 := Nat.le_of_dvd (by have h2 := Equiv.Perm.two_le_of_mem_cycleType hn7; omega) h7n
  have hle3 : n3 ≤ 7 := cycle_length_le_seven σ hn3
  have hne : n3 ≠ n7 := by
    intro hEq
    have h7n3 : 7 ∣ n3 := by simpa [hEq] using h7n
    have hcop : Nat.Coprime 3 7 := by norm_num
    have h21 : 21 ∣ n3 := by
      rw [show (21 : ℕ) = 3 * 7 by norm_num]
      exact hcop.mul_dvd_of_dvd_of_dvd h3n h7n3
    have hn3pos : 0 < n3 := by have h2 := Equiv.Perm.two_le_of_mem_cycleType hn3; omega
    have h21le : 21 ≤ n3 := Nat.le_of_dvd hn3pos h21
    omega
  have hsum := two_mem_sum_ge hn3 hn7 hne
  have hsumle : σ.cycleType.sum ≤ 7 := by
    simpa [Equiv.Perm.sum_cycleType] using Finset.card_le_univ σ.support
  have : 10 ≤ 7 := by omega
  omega

private lemma no_order_35 (x : alternatingGroup (Fin 7)) : orderOf x ≠ 35 := by
  intro h
  let σ : Equiv.Perm (Fin 7) := (x : Equiv.Perm (Fin 7))
  have hσ35 : orderOf σ = 35 := by simpa [σ, Subgroup.orderOf_coe] using h
  have h5 : 5 ∣ orderOf σ := by rw [hσ35]; norm_num
  have h7 : 7 ∣ orderOf σ := by rw [hσ35]; norm_num
  obtain ⟨n5, hn5, h5n⟩ := exists_cycle_length_dvd_of_prime_dvd_order σ Nat.prime_five h5
  obtain ⟨n7, hn7, h7n⟩ := exists_cycle_length_dvd_of_prime_dvd_order σ Nat.prime_seven h7
  have hn5ge : 5 ≤ n5 := Nat.le_of_dvd (by have h2 := Equiv.Perm.two_le_of_mem_cycleType hn5; omega) h5n
  have hn7ge : 7 ≤ n7 := Nat.le_of_dvd (by have h2 := Equiv.Perm.two_le_of_mem_cycleType hn7; omega) h7n
  have hle5 : n5 ≤ 7 := cycle_length_le_seven σ hn5
  have hne : n5 ≠ n7 := by
    intro hEq
    have h7n5 : 7 ∣ n5 := by simpa [hEq] using h7n
    have hcop : Nat.Coprime 5 7 := by norm_num
    have h35 : 35 ∣ n5 := by
      rw [show (35 : ℕ) = 5 * 7 by norm_num]
      exact hcop.mul_dvd_of_dvd_of_dvd h5n h7n5
    have hn5pos : 0 < n5 := by have h2 := Equiv.Perm.two_le_of_mem_cycleType hn5; omega
    have h35le : 35 ≤ n5 := Nat.le_of_dvd hn5pos h35
    omega
  have hsum := two_mem_sum_ge hn5 hn7 hne
  have hsumle : σ.cycleType.sum ≤ 7 := by
    simpa [Equiv.Perm.sum_cycleType] using Finset.card_le_univ σ.support
  have : 12 ≤ 7 := by omega
  omega

private lemma no_order_105 (x : alternatingGroup (Fin 7)) : orderOf x ≠ 105 := by
  intro h
  let σ : Equiv.Perm (Fin 7) := (x : Equiv.Perm (Fin 7))
  have hσ105 : orderOf σ = 105 := by simpa [σ, Subgroup.orderOf_coe] using h
  have h3 : 3 ∣ orderOf σ := by rw [hσ105]; norm_num
  have h5 : 5 ∣ orderOf σ := by rw [hσ105]; norm_num
  have h7 : 7 ∣ orderOf σ := by rw [hσ105]; norm_num
  obtain ⟨n3, hn3, h3n⟩ := exists_cycle_length_dvd_of_prime_dvd_order σ Nat.prime_three h3
  obtain ⟨n5, hn5, h5n⟩ := exists_cycle_length_dvd_of_prime_dvd_order σ Nat.prime_five h5
  obtain ⟨n7, hn7, h7n⟩ := exists_cycle_length_dvd_of_prime_dvd_order σ Nat.prime_seven h7
  have hle3 : n3 ≤ 7 := cycle_length_le_seven σ hn3
  have hle5 : n5 ≤ 7 := cycle_length_le_seven σ hn5
  have h35 : n3 ≠ n5 := by
    intro hEq
    have h5n3 : 5 ∣ n3 := by simpa [hEq] using h5n
    have hcop : Nat.Coprime 3 5 := by norm_num
    have h15 : 15 ∣ n3 := by
      rw [show (15 : ℕ) = 3 * 5 by norm_num]
      exact hcop.mul_dvd_of_dvd_of_dvd h3n h5n3
    have hn3pos : 0 < n3 := by have h2 := Equiv.Perm.two_le_of_mem_cycleType hn3; omega
    have h15le : 15 ≤ n3 := Nat.le_of_dvd hn3pos h15
    omega
  have h37 : n3 ≠ n7 := by
    intro hEq
    have h7n3 : 7 ∣ n3 := by simpa [hEq] using h7n
    have hcop : Nat.Coprime 3 7 := by norm_num
    have h21 : 21 ∣ n3 := by
      rw [show (21 : ℕ) = 3 * 7 by norm_num]
      exact hcop.mul_dvd_of_dvd_of_dvd h3n h7n3
    have hn3pos : 0 < n3 := by have h2 := Equiv.Perm.two_le_of_mem_cycleType hn3; omega
    have h21le : 21 ≤ n3 := Nat.le_of_dvd hn3pos h21
    omega
  have h57 : n5 ≠ n7 := by
    intro hEq
    have h7n5 : 7 ∣ n5 := by simpa [hEq] using h7n
    have hcop : Nat.Coprime 5 7 := by norm_num
    have h35 : 35 ∣ n5 := by
      rw [show (35 : ℕ) = 5 * 7 by norm_num]
      exact hcop.mul_dvd_of_dvd_of_dvd h5n h7n5
    have hn5pos : 0 < n5 := by have h2 := Equiv.Perm.two_le_of_mem_cycleType hn5; omega
    have h35le : 35 ≤ n5 := Nat.le_of_dvd hn5pos h35
    omega
  have hsum := three_mem_sum_ge hn3 hn5 hn7 h35 h37 h57
  have hsumle : σ.cycleType.sum ≤ 7 := by
    simpa [Equiv.Perm.sum_cycleType] using Finset.card_le_univ σ.support
  have : 15 ≤ 7 := by omega
  omega

private lemma no_order_45_63_315 (x : alternatingGroup (Fin 7)) :
    orderOf x ≠ 45 ∧ orderOf x ≠ 63 ∧ orderOf x ≠ 315 := by
  have h420 := orderOf_perm_fin_seven_dvd_420 (x : Equiv.Perm (Fin 7))
  constructor
  · intro h
    have h9 : 9 ∣ orderOf (x : Equiv.Perm (Fin 7)) := by
      have hσ : orderOf (x : Equiv.Perm (Fin 7)) = 45 := by simpa [Subgroup.orderOf_coe] using h
      rw [hσ]
      norm_num
    exact (by norm_num : ¬ 9 ∣ 420) (h9.trans h420)
  · constructor
    · intro h
      have h9 : 9 ∣ orderOf (x : Equiv.Perm (Fin 7)) := by
        have hσ : orderOf (x : Equiv.Perm (Fin 7)) = 63 := by simpa [Subgroup.orderOf_coe] using h
        rw [hσ]
        norm_num
      exact (by norm_num : ¬ 9 ∣ 420) (h9.trans h420)
    · intro h
      have h9 : 9 ∣ orderOf (x : Equiv.Perm (Fin 7)) := by
        have hσ : orderOf (x : Equiv.Perm (Fin 7)) = 315 := by simpa [Subgroup.orderOf_coe] using h
        rw [hσ]
        norm_num
      exact (by norm_num : ¬ 9 ∣ 420) (h9.trans h420)

private lemma sylow_of_order_p
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {x : G} (_hx : x ≠ 1) (hord : orderOf x = p) :
    ∃ P : Sylow p G, x ∈ (P : Subgroup G) := by
  let Z : Subgroup G := Subgroup.zpowers x
  have hZp : IsPGroup p Z := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hord, pow_one]
  obtain ⟨P, hZP⟩ := IsPGroup.exists_le_sylow (p := p) hZp
  exact ⟨P, hZP (Subgroup.mem_zpowers x)⟩

private lemma eq_of_order_p_mem_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q : Sylow p G} (hPcard : Nat.card (P : Subgroup G) = p)
    (hQcard : Nat.card (Q : Subgroup G) = p)
    {x : G} (hxP : x ∈ (P : Subgroup G)) (hxQ : x ∈ (Q : Subgroup G))
    (_hx : x ≠ 1) (hord : orderOf x = p) : P = Q := by
  have hPz : (P : Subgroup G) = Subgroup.zpowers x := by
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxP) (by
      rw [hPcard, Nat.card_zpowers, hord])).symm
  have hQz : (Q : Subgroup G) = Subgroup.zpowers x := by
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxQ) (by
      rw [hQcard, Nat.card_zpowers, hord])).symm
  exact Sylow.ext (hPz.trans hQz.symm)

private lemma card_order_p_elements_eq_sylow_mul
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [Fintype (Sylow p G)]
    (hPcard : ∀ P : Sylow p G, Nat.card (P : Subgroup G) = p) :
    Nat.card {x : G // x ≠ 1 ∧ orderOf x = p} =
      Nat.card (Sylow p G) * (p - 1) := by
  classical
  let α := Σ P : Sylow p G, {x : ↥(P : Subgroup G) // x ≠ 1}
  let β := {x : G // x ≠ 1 ∧ orderOf x = p}
  let f : α → β := fun q =>
    ⟨(q.2 : G), ⟨(by intro hx; exact q.2.2 (Subtype.ext hx)),
      (by
        have hPp : IsPGroup p (q.1 : Subgroup G) := q.1.isPGroup'
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hPp) q.2
        have hkG : orderOf (q.2 : G) = p ^ k := by simpa [Subgroup.orderOf_coe] using hk
        have hdvd : orderOf (q.2 : G) ∣ Nat.card (q.1 : Subgroup G) :=
          Subgroup.orderOf_dvd_natCard (q.1 : Subgroup G) q.2.1.2
        rw [hkG, hPcard q.1] at hdvd
        have hk1 : 1 ≤ k := by
          by_contra hk0
          have hk0' : k = 0 := by omega
          have hx1 : orderOf (q.2 : G) = 1 := by simpa [hk0'] using hkG
          apply q.2.2
          apply Subtype.ext
          exact orderOf_eq_one_iff.mp hx1
        have hk_le : k ≤ 1 := by
          have hp_fac : p.factorization p = 1 := (Fact.out : Nat.Prime p).factorization_self
          rw [← hp_fac]
          exact (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out : Nat.Prime p) (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))).mp hdvd
        have hk_eq : k = 1 := by omega
        simpa [hk_eq] using hkG)⟩⟩
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨P, hyP⟩ := sylow_of_order_p (p := p) y.2.1 y.2.2
    refine ⟨⟨P, ⟨⟨y.1, hyP⟩, ?_⟩⟩, rfl⟩
    · intro hzero
      apply y.2.1
      exact congrArg (fun z : ↥(P : Subgroup G) => (z : G)) hzero
  have hinj : Function.Injective f := by
    rintro ⟨Pq, xq⟩ ⟨Pr, xr⟩ hq
    have hx : (xq : G) = (xr : G) := congrArg (fun z : β => (z : G)) hq
    have hqP : (xq : G) ∈ (Pq : Subgroup G) := xq.1.2
    have hrP : (xr : G) ∈ (Pr : Subgroup G) := xr.1.2
    have hordr : orderOf (xr : G) = p := (f ⟨Pr, xr⟩).2.2
    have hordq : orderOf (xq : G) = p := by rw [hx, hordr]
    have hxqne : xq.1 ≠ 1 := xq.2
    have hxrne : xr.1 ≠ 1 := xr.2
    have hne_q : (xq : G) ≠ 1 := by
      intro h1
      exact hxqne (Subtype.ext h1)
    have hne_r : (xr : G) ≠ 1 := by
      intro h1
      exact hxrne (Subtype.ext h1)
    have hPQ : (Pq : Subgroup G) = (Pr : Subgroup G) := by
      have hqr : Pq = Pr := eq_of_order_p_mem_sylow (p := p) (P := Pq) (Q := Pr)
        (hPcard Pq) (hPcard Pr) hqP (by simpa [hx] using hrP) hne_q hordq
      exact congrArg (fun P : Sylow p G => (P : Subgroup G)) hqr
    have hPqPr : Pq = Pr := Sylow.ext hPQ
    subst Pr
    have hxSub : xq.1 = xr.1 := by
      apply Subtype.ext
      exact hx
    exact congrArg (Sigma.mk Pq) (Subtype.ext hxSub)
  have hα : Nat.card α = ∑ P : Sylow p G, Nat.card {x : ↥(P : Subgroup G) // x ≠ 1} := Nat.card_sigma
  have hpair (P : Sylow p G) :
      Nat.card {x : ↥(P : Subgroup G) // x ≠ 1} = p - 1 := by
    letI : Fintype (P : Subgroup G) := Fintype.ofFinite _
    letI : Fintype {x : ↥(P : Subgroup G) // x ≠ 1} := Fintype.ofFinite _
    letI : Fintype {x : ↥(P : Subgroup G) // x = 1} := Fintype.ofFinite _
    have h1 : Fintype.card {x : ↥(P : Subgroup G) // x = 1} = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨1, rfl⟩, ?_⟩
      intro x
      apply Subtype.ext
      simpa using x.2
    have hsplit := Fintype.card_subtype_compl (α := ↥(P : Subgroup G))
      (p := fun x : ↥(P : Subgroup G) => x = 1)
    rw [h1] at hsplit
    have hcardP : Fintype.card (P : Subgroup G) = p := by
      rw [← Nat.card_eq_fintype_card, hPcard P]
    rw [Nat.card_eq_fintype_card]
    rw [hcardP] at hsplit
    simpa using hsplit
  have hcardβ : Nat.card β = Nat.card α := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm
  calc
    Nat.card β = Nat.card α := hcardβ
    _ = ∑ P : Sylow p G, Nat.card {x : ↥(P : Subgroup G) // x ≠ 1} := hα
    _ = ∑ P : Sylow p G, (p - 1) := by simp [hpair]
    _ = Nat.card (Sylow p G) * (p - 1) := by
      simp [Finset.sum_const, Nat.card_eq_fintype_card]

private lemma top_subgroup_centralizes_normal_prime_order_subgroup_of_coprime
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hNcard : Nat.card N = p)
    (hcop : Nat.Coprime (Nat.card G) (p - 1)) :
    (⊤ : Subgroup G) ≤ Subgroup.centralizer (N : Set G) := by
  classical
  letI : IsCyclic N := isCyclic_of_prime_card hNcard
  let φ : G →* MulAut N := MulAut.conjNormal (H := N)
  have hrange_dvd_G : Nat.card φ.range ∣ Nat.card G := Subgroup.card_range_dvd φ
  have hcardAut : Nat.card (MulAut N) = p - 1 := by
    rw [IsCyclic.card_mulAut, hNcard, Nat.totient_prime (Fact.out : Nat.Prime p)]
  have hrange_dvd_aut : Nat.card φ.range ∣ p - 1 := by
    rw [← hcardAut]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have hd1 : Nat.card φ.range = 1 := Nat.eq_one_of_dvd_coprimes hcop hrange_dvd_G hrange_dvd_aut
  have hbot : φ.range = ⊥ := (Subgroup.card_eq_one (H := φ.range)).1 hd1
  intro g hg
  have hφ : φ g = 1 := by
    have hmem : φ g ∈ φ.range := ⟨g, rfl⟩
    simpa [hbot] using hmem
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let n : N := ⟨y, hy⟩
  have hfix : MulAut.conjNormal (G := G) (H := N) g n = n := by
    simpa [φ, hφ]
  have hval := congrArg Subtype.val hfix
  change g * (y : G) * g⁻¹ = y at hval
  have hcomm : g * (y : G) = (y : G) * g := by
    calc
      g * (y : G) = (g * (y : G) * g⁻¹) * g := by group
      _ = (y : G) * g := by rw [hval]
  exact hcomm.symm

private lemma exists_order_three_centralizing_normal_seven
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hNcard : Nat.card N = 7) (hGcard : Nat.card G = 63) :
    ∃ z : G, z ≠ 1 ∧ z ^ 3 = 1 ∧ z ∈ Subgroup.centralizer (N : Set G) := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : IsCyclic N := isCyclic_of_prime_card hNcard
  let φ : G →* MulAut N := MulAut.conjNormal (H := N)
  have hrange_dvd_G : Nat.card φ.range ∣ 63 := by simpa [hGcard] using Subgroup.card_range_dvd φ
  have hcardAut : Nat.card (MulAut N) = 6 := by
    rw [IsCyclic.card_mulAut, hNcard, Nat.totient_prime Nat.prime_seven]
  have hrange_dvd_aut : Nat.card φ.range ∣ 6 := by
    rw [← hcardAut]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have hd_le : Nat.card φ.range ≤ 6 := Nat.le_of_dvd (by norm_num : 0 < 6) hrange_dvd_aut
  have hprod : Nat.card φ.ker * Nat.card φ.range = 63 := by
    have h := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hGcard] at h
    exact h
  have h3ker : 3 ∣ Nat.card φ.ker := by
    have hd_cases : Nat.card φ.range = 1 ∨ Nat.card φ.range = 3 := by
      interval_cases d : Nat.card φ.range
      · norm_num at hrange_dvd_aut
      · left
        omega
      · norm_num at hrange_dvd_G
      · right
        omega
      · norm_num at hrange_dvd_G
      · norm_num at hrange_dvd_aut
      · norm_num at hrange_dvd_G
    rcases hd_cases with hd1 | hd3
    · have hker : Nat.card φ.ker = 63 := by
        rw [hd1] at hprod
        omega
      rw [hker]
      norm_num
    · have hker : Nat.card φ.ker = 21 := by
        rw [hd3] at hprod
        omega
      rw [hker]
      norm_num
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 3 h3ker
  let z : G := y
  have hz_ne : z ≠ 1 := by
    intro hz
    have hy1 : y = 1 := by
      apply Subtype.ext
      exact hz
    have hord1 : orderOf y = 1 := by rw [hy1]; simp
    have hbad : (3 : ℕ) = 1 := by rw [← hy, hord1]
    exact Nat.prime_three.ne_one hbad
  have hz_pow : z ^ 3 = 1 := by
    have hzord : orderOf z = 3 := by
      change orderOf (y : G) = 3
      rw [Subgroup.orderOf_coe]
      exact hy
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hzord])
  have hz_ker : z ∈ φ.ker := y.2
  have hz_cent : z ∈ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n0 hn0
    let n : N := ⟨n0, hn0⟩
    have hφz : φ z = 1 := by
      simpa [MonoidHom.mem_ker] using hz_ker
    have hfix : MulAut.conjNormal (G := G) (H := N) z n = n := by
      simpa [φ, hφz]
    have hval := congrArg Subtype.val hfix
    change z * (n0 : G) * z⁻¹ = n0 at hval
    have hcomm : z * (n0 : G) = (n0 : G) * z := by
      calc
        z * (n0 : G) = (z * (n0 : G) * z⁻¹) * z := by group
        _ = (n0 : G) * z := by rw [hval]
    exact hcomm.symm
  exact ⟨z, hz_ne, hz_pow, hz_cent⟩

private lemma sylow_index_eq
    {G : Type*} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hG : Nat.card G = p * m)
    (hPcard : Nat.card (P : Subgroup G) = p) : P.index = m := by
  have h := Subgroup.card_mul_index (P : Subgroup G)
  rw [hPcard, hG] at h
  exact Nat.mul_left_cancel (Nat.Prime.pos (Fact.out : Nat.Prime p)) h

private lemma sylow_count_data
    {G : Type*} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    [Fintype (Sylow p G)] (P : Sylow p G) (hindex : P.index = m) (hm : 0 < m) :
    Nat.card (Sylow p G) ≤ m ∧
      Nat.card (Sylow p G) ≡ 1 [MOD p] ∧
        Nat.card (Sylow p G) ∣ m := by
  have hdvd : Nat.card (Sylow p G) ∣ P.index := P.card_dvd_index
  have hle : Nat.card (Sylow p G) ≤ m := Nat.le_of_dvd hm (by simpa [hindex] using hdvd)
  exact ⟨hle, card_sylow_modEq_one (G := G) (p := p), by simpa [hindex] using hdvd⟩

private lemma sylow_normal_of_count_one
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [Fintype (Sylow p G)] (hcount : Nat.card (Sylow p G) = 1) (P : Sylow p G) :
    (P : Subgroup G).Normal := by
  letI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hcount).1
  exact Sylow.normal_of_subsingleton P

private lemma order_mul_of_commute_coprime
    {G : Type*} [Group G] (a b : G) (hcomm : a * b = b * a)
    {p q n : ℕ} (ha : orderOf a = p) (hb : orderOf b = q)
    (hcop : Nat.Coprime p q) (hn : p * q = n) : orderOf (a * b) = n := by
  have hco : (orderOf a).Coprime (orderOf b) := by rwa [ha, hb]
  have hc : Commute a b := hcomm
  rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime hco, ha, hb, hn]

private lemma factorization_35_5 : (35 : ℕ).factorization 5 = 1 := by
  rw [show (35 : ℕ) = 5 * 7 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.prime_five.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 7)]

private lemma factorization_35_7 : (35 : ℕ).factorization 7 = 1 := by
  rw [show (35 : ℕ) = 7 * 5 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.prime_seven.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 5)]

private lemma card_not_35 (X : Subgroup (alternatingGroup (Fin 7)))
    (hX : Nat.card X = 35) : False := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  letI : Fintype (Sylow 5 X) := Fintype.ofFinite _
  letI : Fintype (Sylow 7 X) := Fintype.ofFinite _
  let P5 : Sylow 5 X := default
  let P7 : Sylow 7 X := default
  have h5card : Nat.card (P5 : Subgroup X) = 5 := by
    rw [Sylow.card_eq_multiplicity, hX, factorization_35_5]
    norm_num
  have h7card : Nat.card (P7 : Subgroup X) = 7 := by
    rw [Sylow.card_eq_multiplicity, hX, factorization_35_7]
    norm_num
  have h5index : (P5 : Subgroup X).index = 7 := by
    apply sylow_index_eq (p := 5) (m := 7)
    · rw [hX]
    · exact h5card
  have h7index : (P7 : Subgroup X).index = 5 := by
    apply sylow_index_eq (p := 7) (m := 5)
    · rw [hX]
    · exact h7card
  have h5count : Nat.card (Sylow 5 X) = 1 := by
    rcases sylow_count_data (G := X) (p := 5) P5 h5index (by norm_num) with ⟨hnle, hnmod, hndvd⟩
    have hnmod' : Nat.card (Sylow 5 X) % 5 = 1 % 5 := hnmod
    interval_cases n : Nat.card (Sylow 5 X)
    all_goals try norm_num at hnmod' hndvd hnle
    all_goals try omega
  have h7count : Nat.card (Sylow 7 X) = 1 := by
    rcases sylow_count_data (G := X) (p := 7) P7 h7index (by norm_num) with ⟨hnle, hnmod, hndvd⟩
    have hnmod' : Nat.card (Sylow 7 X) % 7 = 1 % 7 := hnmod
    interval_cases n : Nat.card (Sylow 7 X)
    all_goals try norm_num at hnmod' hndvd hnle
    all_goals try omega
  haveI : (P5 : Subgroup X).Normal := sylow_normal_of_count_one h5count P5
  have hcopX : Nat.Coprime (Nat.card X) 4 := by rw [hX]; norm_num
  have hcent : (⊤ : Subgroup X) ≤ Subgroup.centralizer ((P5 : Subgroup X) : Set X) :=
    top_subgroup_centralizes_normal_prime_order_subgroup_of_coprime
      (G := X) (p := 5) (N := (P5 : Subgroup X)) h5card hcopX
  have h7dvd : 7 ∣ Nat.card X := by rw [hX]; norm_num
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := X) 7 h7dvd
  have h5dvd : 5 ∣ Nat.card (P5 : Subgroup X) := by rw [h5card]
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P5 : Subgroup X)) 5 h5dvd
  have ha_cent : (a : X) ∈ Subgroup.centralizer ((P5 : Subgroup X) : Set X) :=
    hcent (by simp)
  have hcomm : a * (b : X) = (b : X) * a := by
    exact (Subgroup.mem_centralizer_iff.mp ha_cent (b : X) b.2).symm
  have hbord : orderOf (b : X) = 5 := by simpa [Subgroup.orderOf_coe] using hb
  have hprod : orderOf (a * (b : X)) = 35 :=
    order_mul_of_commute_coprime a (b : X) hcomm ha hbord (by norm_num) (by norm_num)
  let c : X := a * (b : X)
  have hprodG : orderOf (c : alternatingGroup (Fin 7)) = 35 := by
    change orderOf ((a * (b : X) : X) : alternatingGroup (Fin 7)) = 35
    rw [Subgroup.orderOf_coe]
    exact hprod
  exact no_order_35 (c : alternatingGroup (Fin 7)) hprodG


private lemma factorization_45_3 : (45 : ℕ).factorization 3 = 2 := by
  rw [show (45 : ℕ) = 3 ^ 2 * 5 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_pow]
  simp [Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 5)]

private lemma factorization_45_5 : (45 : ℕ).factorization 5 = 1 := by
  rw [show (45 : ℕ) = 5 * 9 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.prime_five.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 9)]

private lemma factorization_63_3 : (63 : ℕ).factorization 3 = 2 := by
  rw [show (63 : ℕ) = 3 ^ 2 * 7 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_pow]
  simp [Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 7)]

private lemma factorization_63_7 : (63 : ℕ).factorization 7 = 1 := by
  rw [show (63 : ℕ) = 7 * 9 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.prime_seven.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 9)]

private lemma card_not_45 (X : Subgroup (alternatingGroup (Fin 7)))
    (hX : Nat.card X = 45) : False := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI : Fintype (Sylow 3 X) := Fintype.ofFinite _
  letI : Fintype (Sylow 5 X) := Fintype.ofFinite _
  let P3 : Sylow 3 X := default
  let P5 : Sylow 5 X := default
  have h3card : Nat.card (P3 : Subgroup X) = 9 := by
    rw [Sylow.card_eq_multiplicity, hX, factorization_45_3]
    norm_num
  have h5card : Nat.card (P5 : Subgroup X) = 5 := by
    rw [Sylow.card_eq_multiplicity, hX, factorization_45_5]
    norm_num
  have h3index : (P3 : Subgroup X).index = 5 := by
    have h := Subgroup.card_mul_index (P3 : Subgroup X)
    rw [h3card, hX] at h
    omega
  have h5index : (P5 : Subgroup X).index = 9 := by
    apply sylow_index_eq (p := 5) (m := 9)
    · rw [hX]
    · exact h5card
  have h3count : Nat.card (Sylow 3 X) = 1 := by
    rcases sylow_count_data (G := X) (p := 3) P3 h3index (by norm_num) with ⟨hnle, hnmod, hndvd⟩
    have hnmod' : Nat.card (Sylow 3 X) % 3 = 1 % 3 := hnmod
    interval_cases n : Nat.card (Sylow 3 X)
    all_goals try norm_num at hnmod' hndvd hnle
    all_goals try omega
  have h5count : Nat.card (Sylow 5 X) = 1 := by
    rcases sylow_count_data (G := X) (p := 5) P5 h5index (by norm_num) with ⟨hnle, hnmod, hndvd⟩
    have hnmod' : Nat.card (Sylow 5 X) % 5 = 1 % 5 := hnmod
    interval_cases n : Nat.card (Sylow 5 X)
    all_goals try norm_num at hnmod' hndvd hnle
    all_goals try omega
  haveI : (P5 : Subgroup X).Normal := sylow_normal_of_count_one h5count P5
  have hcopX : Nat.Coprime (Nat.card X) 4 := by rw [hX]; norm_num
  have hcent : (⊤ : Subgroup X) ≤ Subgroup.centralizer ((P5 : Subgroup X) : Set X) :=
    top_subgroup_centralizes_normal_prime_order_subgroup_of_coprime
      (G := X) (p := 5) (N := (P5 : Subgroup X)) h5card hcopX
  have h3dvd : 3 ∣ Nat.card X := by rw [hX]; norm_num
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3dvd
  have h5dvd : 5 ∣ Nat.card (P5 : Subgroup X) := by rw [h5card]
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P5 : Subgroup X)) 5 h5dvd
  have ha_cent : (a : X) ∈ Subgroup.centralizer ((P5 : Subgroup X) : Set X) := hcent (by simp)
  have hcomm : a * (b : X) = (b : X) * a :=
    (Subgroup.mem_centralizer_iff.mp ha_cent (b : X) b.2).symm
  have hbord : orderOf (b : X) = 5 := by simpa [Subgroup.orderOf_coe] using hb
  have hprod : orderOf (a * (b : X)) = 15 :=
    order_mul_of_commute_coprime a (b : X) hcomm ha hbord (by norm_num) (by norm_num)
  let c : X := a * (b : X)
  have hprodG : orderOf (c : alternatingGroup (Fin 7)) = 15 := by
    change orderOf ((a * (b : X) : X) : alternatingGroup (Fin 7)) = 15
    rw [Subgroup.orderOf_coe]
    exact hprod
  exact no_order_15 (c : alternatingGroup (Fin 7)) hprodG

private lemma card_not_63 (X : Subgroup (alternatingGroup (Fin 7)))
    (hX : Nat.card X = 63) : False := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  letI : Fintype (Sylow 7 X) := Fintype.ofFinite _
  let P7 : Sylow 7 X := default
  have h7card : Nat.card (P7 : Subgroup X) = 7 := by
    rw [Sylow.card_eq_multiplicity, hX, factorization_63_7]
    norm_num
  have h7index : (P7 : Subgroup X).index = 9 := by
    apply sylow_index_eq (p := 7) (m := 9)
    · rw [hX]
    · exact h7card
  have h7count : Nat.card (Sylow 7 X) = 1 := by
    rcases sylow_count_data (G := X) (p := 7) P7 h7index (by norm_num) with ⟨hnle, hnmod, hndvd⟩
    have hnmod' : Nat.card (Sylow 7 X) % 7 = 1 % 7 := hnmod
    interval_cases n : Nat.card (Sylow 7 X)
    all_goals try norm_num at hnmod' hndvd hnle
    all_goals try omega
  haveI : (P7 : Subgroup X).Normal := sylow_normal_of_count_one h7count P7
  obtain ⟨z, hzne, hzpow, hzcent⟩ :=
    exists_order_three_centralizing_normal_seven (G := X) (N := (P7 : Subgroup X)) h7card hX
  have h7dvd : 7 ∣ Nat.card (P7 : Subgroup X) := by rw [h7card]
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P7 : Subgroup X)) 7 h7dvd
  have hcomm : z * (b : X) = (b : X) * z :=
    (Subgroup.mem_centralizer_iff.mp hzcent (b : X) b.2).symm
  have hbord : orderOf (b : X) = 7 := by simpa [Subgroup.orderOf_coe] using hb
  have hzord : orderOf z = 3 := by
    exact orderOf_eq_prime hzpow hzne
  have hprod : orderOf (z * (b : X)) = 21 :=
    order_mul_of_commute_coprime z (b : X) hcomm hzord hbord (by norm_num) (by norm_num)
  let c : X := z * (b : X)
  have hprodG : orderOf (c : alternatingGroup (Fin 7)) = 21 := by
    change orderOf ((z * (b : X) : X) : alternatingGroup (Fin 7)) = 21
    rw [Subgroup.orderOf_coe]
    exact hprod
  exact no_order_21 (c : alternatingGroup (Fin 7)) hprodG


private lemma card_ge_one_add_order_counts
    {G : Type*} [Group G] [Finite G] {n5 n7 : ℕ}
    (h5 : Nat.card {x : G // x ≠ 1 ∧ orderOf x = 5} = n5 * 4)
    (h7 : Nat.card {x : G // x ≠ 1 ∧ orderOf x = 7} = n7 * 6) :
    1 + n5 * 4 + n7 * 6 ≤ Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let S : Finset G := Finset.univ.filter (fun x : G => x ≠ 1)
  let A : Finset G := S.filter (fun x : G => orderOf x = 5)
  let B : Finset G := S.filter (fun x : G => orderOf x = 7)
  have hcardG : Nat.card G = 1 + S.card := by
    rw [Nat.card_eq_fintype_card]
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
      (p := fun x : G => x ≠ 1)
    have hone : (Finset.univ.filter fun x : G => x = 1).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨1, ?_⟩
      ext x
      simp
    have hnot : (Finset.univ.filter fun x : G => ¬ x ≠ 1) =
        (Finset.univ.filter fun x : G => x = 1) := by
      ext x
      simp
    rw [hnot, hone] at hsplit
    change Finset.univ.card = 1 + S.card
    rw [show S.card = (Finset.univ.filter fun x : G => x ≠ 1).card by rfl]
    rw [← hsplit, Nat.add_comm]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_filter]
    intro x hx h5x h7x
    omega
  have hcardA : A.card = n5 * 4 := by
    have hA : Fintype.card {x : G // x ∈ A} = A.card :=
      Fintype.card_of_subtype A (by intro x; simp [A, S])
    rw [← hA]
    have hEq : Nat.card {x : G // x ∈ A} = Nat.card {x : G // x ≠ 1 ∧ orderOf x = 5} := by
      exact Nat.card_congr (Equiv.subtypeEquivRight (by intro x; simp [A, S]))
    rw [← Nat.card_eq_fintype_card, hEq, h5]
  have hcardB : B.card = n7 * 6 := by
    have hB : Fintype.card {x : G // x ∈ B} = B.card :=
      Fintype.card_of_subtype B (by intro x; simp [B, S])
    rw [← hB]
    have hEq : Nat.card {x : G // x ∈ B} = Nat.card {x : G // x ≠ 1 ∧ orderOf x = 7} := by
      exact Nat.card_congr (Equiv.subtypeEquivRight (by intro x; simp [B, S]))
    rw [← Nat.card_eq_fintype_card, hEq, h7]
  have hunion : (A ∪ B).card = n5 * 4 + n7 * 6 := by
    rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardB]
  have hsub : A ∪ B ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact (Finset.mem_filter.mp hxA).1
    · exact (Finset.mem_filter.mp hxB).1
  have hle : (A ∪ B).card ≤ S.card := Finset.card_le_card hsub
  rw [hcardG]
  omega


private lemma exists_order_five_centralizing_normal_seven_of_card_105
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hNcard : Nat.card N = 7) (hGcard : Nat.card G = 105) :
    ∃ z : G, z ≠ 1 ∧ orderOf z = 5 ∧ z ∈ Subgroup.centralizer (N : Set G) := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI : IsCyclic N := isCyclic_of_prime_card hNcard
  let φ : G →* MulAut N := MulAut.conjNormal (H := N)
  have hrange_dvd_G : Nat.card φ.range ∣ 105 := by simpa [hGcard] using Subgroup.card_range_dvd φ
  have hcardAut : Nat.card (MulAut N) = 6 := by
    rw [IsCyclic.card_mulAut, hNcard, Nat.totient_prime Nat.prime_seven]
  have hrange_dvd_aut : Nat.card φ.range ∣ 6 := by
    rw [← hcardAut]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have hd_le : Nat.card φ.range ≤ 6 := Nat.le_of_dvd (by norm_num : 0 < 6) hrange_dvd_aut
  have hprod : Nat.card φ.ker * Nat.card φ.range = 105 := by
    have h := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hGcard] at h
    exact h
  have h5ker : 5 ∣ Nat.card φ.ker := by
    have hd_cases : Nat.card φ.range = 1 ∨ Nat.card φ.range = 3 := by
      interval_cases d : Nat.card φ.range
      · norm_num at hrange_dvd_aut
      · left
        omega
      · norm_num at hrange_dvd_G
      · right
        omega
      · norm_num at hrange_dvd_G
      · norm_num at hrange_dvd_aut
      · norm_num at hrange_dvd_G
    rcases hd_cases with hd1 | hd3
    · have hker : Nat.card φ.ker = 105 := by
        rw [hd1] at hprod
        omega
      rw [hker]
      norm_num
    · have hker : Nat.card φ.ker = 35 := by
        rw [hd3] at hprod
        omega
      rw [hker]
      norm_num
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 5 h5ker
  let z : G := y
  have hz_ne : z ≠ 1 := by
    intro hz
    have hy1 : y = 1 := by apply Subtype.ext; exact hz
    have hord1 : orderOf y = 1 := by rw [hy1]; simp
    have hbad : (5 : ℕ) = 1 := by rw [← hy, hord1]
    exact Nat.prime_five.ne_one hbad
  have hz_ord : orderOf z = 5 := by
    change orderOf (y : G) = 5
    rw [Subgroup.orderOf_coe]
    exact hy
  have hz_ker : z ∈ φ.ker := y.2
  have hz_cent : z ∈ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n0 hn0
    let n : N := ⟨n0, hn0⟩
    have hφz : φ z = 1 := by simpa [MonoidHom.mem_ker] using hz_ker
    have hfix : MulAut.conjNormal (G := G) (H := N) z n = n := by simpa [φ, hφz]
    have hval := congrArg Subtype.val hfix
    change z * (n0 : G) * z⁻¹ = n0 at hval
    have hcomm : z * (n0 : G) = (n0 : G) * z := by
      calc
        z * (n0 : G) = (z * (n0 : G) * z⁻¹) * z := by group
        _ = (n0 : G) * z := by rw [hval]
    exact hcomm.symm
  exact ⟨z, hz_ne, hz_ord, hz_cent⟩

private lemma exists_order_seven_centralizing_normal_five_of_card_105
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hNcard : Nat.card N = 5) (hGcard : Nat.card G = 105) :
    ∃ z : G, z ≠ 1 ∧ orderOf z = 7 ∧ z ∈ Subgroup.centralizer (N : Set G) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  letI : IsCyclic N := isCyclic_of_prime_card hNcard
  let φ : G →* MulAut N := MulAut.conjNormal (H := N)
  have hrange_dvd_G : Nat.card φ.range ∣ 105 := by simpa [hGcard] using Subgroup.card_range_dvd φ
  have hcardAut : Nat.card (MulAut N) = 4 := by
    rw [IsCyclic.card_mulAut, hNcard, Nat.totient_prime Nat.prime_five]
  have hrange_dvd_aut : Nat.card φ.range ∣ 4 := by
    rw [← hcardAut]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have hd_le : Nat.card φ.range ≤ 4 := Nat.le_of_dvd (by norm_num : 0 < 4) hrange_dvd_aut
  have hprod : Nat.card φ.ker * Nat.card φ.range = 105 := by
    have h := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hGcard] at h
    exact h
  have h7ker : 7 ∣ Nat.card φ.ker := by
    have hd1 : Nat.card φ.range = 1 := by
      interval_cases d : Nat.card φ.range
      · norm_num at hrange_dvd_aut
      · omega
      · norm_num at hrange_dvd_G
      · norm_num at hrange_dvd_aut
      · norm_num at hrange_dvd_G
    have hker : Nat.card φ.ker = 105 := by
      rw [hd1] at hprod
      omega
    rw [hker]
    norm_num
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 7 h7ker
  let z : G := y
  have hz_ne : z ≠ 1 := by
    intro hz
    have hy1 : y = 1 := by apply Subtype.ext; exact hz
    have hord1 : orderOf y = 1 := by rw [hy1]; simp
    have hbad : (7 : ℕ) = 1 := by rw [← hy, hord1]
    exact Nat.prime_seven.ne_one hbad
  have hz_ord : orderOf z = 7 := by
    change orderOf (y : G) = 7
    rw [Subgroup.orderOf_coe]
    exact hy
  have hz_ker : z ∈ φ.ker := y.2
  have hz_cent : z ∈ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n0 hn0
    let n : N := ⟨n0, hn0⟩
    have hφz : φ z = 1 := by simpa [MonoidHom.mem_ker] using hz_ker
    have hfix : MulAut.conjNormal (G := G) (H := N) z n = n := by simpa [φ, hφz]
    have hval := congrArg Subtype.val hfix
    change z * (n0 : G) * z⁻¹ = n0 at hval
    have hcomm : z * (n0 : G) = (n0 : G) * z := by
      calc
        z * (n0 : G) = (z * (n0 : G) * z⁻¹) * z := by group
        _ = (n0 : G) * z := by rw [hval]
    exact hcomm.symm
  exact ⟨z, hz_ne, hz_ord, hz_cent⟩

private lemma factorization_105_3 : (105 : ℕ).factorization 3 = 1 := by
  rw [show (105 : ℕ) = 3 * 35 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 35)]

private lemma factorization_105_5 : (105 : ℕ).factorization 5 = 1 := by
  rw [show (105 : ℕ) = 5 * 21 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.prime_five.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 21)]

private lemma factorization_105_7 : (105 : ℕ).factorization 7 = 1 := by
  rw [show (105 : ℕ) = 7 * 15 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.prime_seven.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 15)]


private lemma card_not_105 (X : Subgroup (alternatingGroup (Fin 7)))
    (hX : Nat.card X = 105) : False := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  letI : Fintype (Sylow 5 X) := Fintype.ofFinite _
  letI : Fintype (Sylow 7 X) := Fintype.ofFinite _
  let P5 : Sylow 5 X := default
  let P7 : Sylow 7 X := default
  have h5card : Nat.card (P5 : Subgroup X) = 5 := by
    rw [Sylow.card_eq_multiplicity, hX, factorization_105_5]
    norm_num
  have h7card : Nat.card (P7 : Subgroup X) = 7 := by
    rw [Sylow.card_eq_multiplicity, hX, factorization_105_7]
    norm_num
  have h5index : (P5 : Subgroup X).index = 21 := by
    apply sylow_index_eq (p := 5) (m := 21)
    · rw [hX]
    · exact h5card
  have h7index : (P7 : Subgroup X).index = 15 := by
    apply sylow_index_eq (p := 7) (m := 15)
    · rw [hX]
    · exact h7card
  have h7cases : Nat.card (Sylow 7 X) = 1 ∨ Nat.card (Sylow 7 X) = 15 := by
    rcases sylow_count_data (G := X) (p := 7) P7 h7index (by norm_num) with ⟨hnle, hnmod, hndvd⟩
    have hnmod' : Nat.card (Sylow 7 X) % 7 = 1 % 7 := hnmod
    interval_cases n : Nat.card (Sylow 7 X)
    all_goals try norm_num at hnmod' hndvd hnle
    all_goals try (left; omega)
    all_goals try (right; omega)
  have h5cases : Nat.card (Sylow 5 X) = 1 ∨ Nat.card (Sylow 5 X) = 21 := by
    rcases sylow_count_data (G := X) (p := 5) P5 h5index (by norm_num) with ⟨hnle, hnmod, hndvd⟩
    have hnmod' : Nat.card (Sylow 5 X) % 5 = 1 % 5 := hnmod
    interval_cases n : Nat.card (Sylow 5 X)
    all_goals try norm_num at hnmod' hndvd hnle
    all_goals try (left; omega)
    all_goals try (right; omega)
  rcases h7cases with h7one | h7fifteen
  · haveI : (P7 : Subgroup X).Normal := sylow_normal_of_count_one h7one P7
    obtain ⟨z, hzne, hzord, hzcent⟩ :=
      exists_order_five_centralizing_normal_seven_of_card_105 (G := X) (N := (P7 : Subgroup X)) h7card hX
    have h7dvd : 7 ∣ Nat.card (P7 : Subgroup X) := by rw [h7card]
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P7 : Subgroup X)) 7 h7dvd
    have hcomm : z * (b : X) = (b : X) * z :=
      (Subgroup.mem_centralizer_iff.mp hzcent (b : X) b.2).symm
    have hbord : orderOf (b : X) = 7 := by simpa [Subgroup.orderOf_coe] using hb
    have hprod : orderOf (z * (b : X)) = 35 :=
      order_mul_of_commute_coprime z (b : X) hcomm hzord hbord (by norm_num) (by norm_num)
    let c : X := z * (b : X)
    have hprodG : orderOf (c : alternatingGroup (Fin 7)) = 35 := by
      change orderOf ((z * (b : X) : X) : alternatingGroup (Fin 7)) = 35
      rw [Subgroup.orderOf_coe]
      exact hprod
    exact no_order_35 (c : alternatingGroup (Fin 7)) hprodG
  · rcases h5cases with h5one | h5twentyone
    · haveI : (P5 : Subgroup X).Normal := sylow_normal_of_count_one h5one P5
      obtain ⟨z, hzne, hzord, hzcent⟩ :=
        exists_order_seven_centralizing_normal_five_of_card_105 (G := X) (N := (P5 : Subgroup X)) h5card hX
      have h5dvd : 5 ∣ Nat.card (P5 : Subgroup X) := by rw [h5card]
      obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P5 : Subgroup X)) 5 h5dvd
      have hcomm : z * (b : X) = (b : X) * z :=
        (Subgroup.mem_centralizer_iff.mp hzcent (b : X) b.2).symm
      have hbord : orderOf (b : X) = 5 := by simpa [Subgroup.orderOf_coe] using hb
      have hprod : orderOf (z * (b : X)) = 35 :=
        order_mul_of_commute_coprime z (b : X) hcomm hzord hbord (by norm_num) (by norm_num)
      let c : X := z * (b : X)
      have hprodG : orderOf (c : alternatingGroup (Fin 7)) = 35 := by
        change orderOf ((z * (b : X) : X) : alternatingGroup (Fin 7)) = 35
        rw [Subgroup.orderOf_coe]
        exact hprod
      exact no_order_35 (c : alternatingGroup (Fin 7)) hprodG
    · have h5all : ∀ P : Sylow 5 X, Nat.card (P : Subgroup X) = 5 := by
        intro P
        rw [Sylow.card_eq_multiplicity, hX, factorization_105_5]
        norm_num
      have h7all : ∀ P : Sylow 7 X, Nat.card (P : Subgroup X) = 7 := by
        intro P
        rw [Sylow.card_eq_multiplicity, hX, factorization_105_7]
        norm_num
      have h5exact : Nat.card {x : X // x ≠ 1 ∧ orderOf x = 5} = 21 * 4 := by
        rw [card_order_p_elements_eq_sylow_mul (G := X) (p := 5) h5all, h5twentyone]
      have h7exact : Nat.card {x : X // x ≠ 1 ∧ orderOf x = 7} = 15 * 6 := by
        rw [card_order_p_elements_eq_sylow_mul (G := X) (p := 7) h7all, h7fifteen]
      have hle := card_ge_one_add_order_counts (G := X) (n5 := 21) (n7 := 15) h5exact h7exact
      rw [hX] at hle
      norm_num at hle


private lemma odd_divisor_315_cases {n : ℕ} (h315 : n ∣ 315) (hodd : Odd n) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 9 ∨ n = 15 ∨ n = 21 ∨
      n = 35 ∨ n = 45 ∨ n = 63 ∨ n = 105 ∨ n = 315 := by
  have hle : n ≤ 315 := Nat.le_of_dvd (by norm_num) h315
  interval_cases n
  all_goals try norm_num at h315 hodd
  all_goals try (left; omega)
  all_goals try (right; left; omega)
  all_goals try (right; right; left; omega)
  all_goals try (right; right; right; left; omega)
  all_goals try (right; right; right; right; left; omega)
  all_goals try (right; right; right; right; right; left; omega)
  all_goals try (right; right; right; right; right; right; left; omega)
  all_goals try (right; right; right; right; right; right; right; left; omega)
  all_goals try (right; right; right; right; right; right; right; right; left; omega)
  all_goals try (right; right; right; right; right; right; right; right; right; left; omega)
  all_goals try (right; right; right; right; right; right; right; right; right; right; left; omega)
  all_goals try (right; right; right; right; right; right; right; right; right; right; right; omega)

private lemma order_dvd_315_cases {m : ℕ} (hdiv : m ∣ 315) (hne : m ≠ 1)
    (h15 : m ≠ 15) (h21 : m ≠ 21) (h35 : m ≠ 35)
    (h45 : m ≠ 45) (h63 : m ≠ 63) (h105 : m ≠ 105) (h315 : m ≠ 315) :
    (∃ n : ℕ, 1 ≤ n ∧ m = 3 ^ n) ∨ m = 5 ∨ m = 7 := by
  have hle : m ≤ 315 := Nat.le_of_dvd (by norm_num) hdiv
  interval_cases m
  all_goals try (left; refine ⟨1, by norm_num, rfl⟩)
  all_goals try (left; refine ⟨2, by norm_num, rfl⟩)
  all_goals try (right; left; rfl)
  all_goals try (right; right; rfl)
  all_goals simp_all

private lemma factorization_315_3 : (315 : ℕ).factorization 3 = 2 := by
  rw [show (315 : ℕ) = 3 ^ 2 * 35 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_pow]
  simp [Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 35)]

private lemma factorization_315_5 : (315 : ℕ).factorization 5 = 1 := by
  rw [show (315 : ℕ) = 5 * 63 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.prime_five.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 63)]

private lemma factorization_315_7 : (315 : ℕ).factorization 7 = 1 := by
  rw [show (315 : ℕ) = 7 * 45 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.prime_seven.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 45)]

private lemma card_not_315 (X : Subgroup (alternatingGroup (Fin 7)))
    (hX : Nat.card X = 315) : False := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  letI : Fintype (Sylow 3 X) := Fintype.ofFinite _
  letI : Fintype (Sylow 5 X) := Fintype.ofFinite _
  letI : Fintype (Sylow 7 X) := Fintype.ofFinite _
  let P3 : Sylow 3 X := default
  let P5 : Sylow 5 X := default
  let P7 : Sylow 7 X := default
  have h3card : Nat.card (P3 : Subgroup X) = 9 := by
    rw [Sylow.card_eq_multiplicity, hX, factorization_315_3]
    norm_num
  have h5card : Nat.card (P5 : Subgroup X) = 5 := by
    rw [Sylow.card_eq_multiplicity, hX, factorization_315_5]
    norm_num
  have h7card : Nat.card (P7 : Subgroup X) = 7 := by
    rw [Sylow.card_eq_multiplicity, hX, factorization_315_7]
    norm_num
  have h3index : (P3 : Subgroup X).index = 35 := by
    have h := Subgroup.card_mul_index (P3 : Subgroup X)
    rw [h3card, hX] at h
    omega
  have h5index : (P5 : Subgroup X).index = 63 := by
    apply sylow_index_eq (p := 5) (m := 63)
    · rw [hX]
    · exact h5card
  have h7index : (P7 : Subgroup X).index = 45 := by
    apply sylow_index_eq (p := 7) (m := 45)
    · rw [hX]
    · exact h7card
  have h3cases : Nat.card (Sylow 3 X) = 1 ∨ Nat.card (Sylow 3 X) = 7 := by
    rcases sylow_count_data (G := X) (p := 3) P3 h3index (by norm_num) with ⟨hnle, hnmod, hndvd⟩
    have hnmod' : Nat.card (Sylow 3 X) % 3 = 1 % 3 := hnmod
    interval_cases n : Nat.card (Sylow 3 X)
    all_goals try norm_num at hnmod' hndvd hnle
    all_goals try (left; omega)
    all_goals try (right; omega)
  have h5cases : Nat.card (Sylow 5 X) = 1 ∨ Nat.card (Sylow 5 X) = 21 := by
    rcases sylow_count_data (G := X) (p := 5) P5 h5index (by norm_num) with ⟨hnle, hnmod, hndvd⟩
    have hnmod' : Nat.card (Sylow 5 X) % 5 = 1 % 5 := hnmod
    interval_cases n : Nat.card (Sylow 5 X)
    all_goals try norm_num at hnmod' hndvd hnle
    all_goals try (left; omega)
    all_goals try (right; omega)
  have h7cases : Nat.card (Sylow 7 X) = 1 ∨ Nat.card (Sylow 7 X) = 15 := by
    rcases sylow_count_data (G := X) (p := 7) P7 h7index (by norm_num) with ⟨hnle, hnmod, hndvd⟩
    have hnmod' : Nat.card (Sylow 7 X) % 7 = 1 % 7 := hnmod
    interval_cases n : Nat.card (Sylow 7 X)
    all_goals try norm_num at hnmod' hndvd hnle
    all_goals try (left; omega)
    all_goals try (right; omega)
  let n3 : ℕ := Nat.card (Sylow 3 X)
  let n5 : ℕ := Nat.card (Sylow 5 X)
  let n7 : ℕ := Nat.card (Sylow 7 X)
  have h3le : n3 ≤ 7 := by
    rcases h3cases with h | h <;> dsimp [n3] at h ⊢ <;> omega
  have h5le : n5 ≤ 21 := by
    rcases h5cases with h | h <;> dsimp [n5] at h ⊢ <;> omega
  have h7le : n7 ≤ 15 := by
    rcases h7cases with h | h <;> dsimp [n7] at h ⊢ <;> omega
  have hall : ∀ x : X, x ≠ 1 →
      (∃ n : ℕ, 1 ≤ n ∧ orderOf x = 3 ^ n) ∨
      (∃ n : ℕ, 1 ≤ n ∧ orderOf x = 5 ^ n) ∨
      (∃ n : ℕ, 1 ≤ n ∧ orderOf x = 7 ^ n) := by
    intro x hxne
    have hdiv : orderOf x ∣ 315 := by
      rw [← hX]
      exact orderOf_dvd_natCard x
    have hne : orderOf x ≠ 1 := by
      intro h1
      apply hxne
      exact orderOf_eq_one_iff.mp h1
    have h15 : orderOf x ≠ 15 := by
      intro h
      have hG : orderOf (x : alternatingGroup (Fin 7)) = 15 := by
        simpa [Subgroup.orderOf_coe] using h
      exact no_order_15 (x : alternatingGroup (Fin 7)) hG
    have h21 : orderOf x ≠ 21 := by
      intro h
      have hG : orderOf (x : alternatingGroup (Fin 7)) = 21 := by
        simpa [Subgroup.orderOf_coe] using h
      exact no_order_21 (x : alternatingGroup (Fin 7)) hG
    have h35 : orderOf x ≠ 35 := by
      intro h
      have hG : orderOf (x : alternatingGroup (Fin 7)) = 35 := by
        simpa [Subgroup.orderOf_coe] using h
      exact no_order_35 (x : alternatingGroup (Fin 7)) hG
    have hbad := no_order_45_63_315 (x : alternatingGroup (Fin 7))
    have h45 : orderOf x ≠ 45 := by
      intro h
      have hG : orderOf (x : alternatingGroup (Fin 7)) = 45 := by
        simpa [Subgroup.orderOf_coe] using h
      exact hbad.1 hG
    have h63 : orderOf x ≠ 63 := by
      intro h
      have hG : orderOf (x : alternatingGroup (Fin 7)) = 63 := by
        simpa [Subgroup.orderOf_coe] using h
      exact hbad.2.1 hG
    have h105 : orderOf x ≠ 105 := by
      intro h
      have hG : orderOf (x : alternatingGroup (Fin 7)) = 105 := by
        simpa [Subgroup.orderOf_coe] using h
      exact no_order_105 (x : alternatingGroup (Fin 7)) hG
    have h315 : orderOf x ≠ 315 := by
      intro h
      have hG : orderOf (x : alternatingGroup (Fin 7)) = 315 := by
        simpa [Subgroup.orderOf_coe] using h
      exact hbad.2.2 hG
    rcases order_dvd_315_cases hdiv hne h15 h21 h35 h45 h63 h105 h315 with h3 | h5 | h7
    · exact Or.inl h3
    · exact Or.inr (Or.inl ⟨1, by norm_num, h5⟩)
    · exact Or.inr (Or.inr ⟨1, by norm_num, h7⟩)
  have hle := card_nonone_le_sum_powers (G := X) hall
  have h3all : ∀ P : Sylow 3 X, Nat.card (P : Subgroup X) = 9 := by
    intro P
    rw [Sylow.card_eq_multiplicity, hX, factorization_315_3]
    norm_num
  have h5all : ∀ P : Sylow 5 X, Nat.card (P : Subgroup X) = 5 := by
    intro P
    rw [Sylow.card_eq_multiplicity, hX, factorization_315_5]
    norm_num
  have h7all : ∀ P : Sylow 7 X, Nat.card (P : Subgroup X) = 7 := by
    intro P
    rw [Sylow.card_eq_multiplicity, hX, factorization_315_7]
    norm_num
  have hs3 : (∑ P : Sylow 3 X, (Nat.card (P : Subgroup X) - 1)) = n3 * 8 := by
    calc
      (∑ P : Sylow 3 X, (Nat.card (P : Subgroup X) - 1))
          = ∑ P : Sylow 3 X, 8 := by
            refine Finset.sum_congr rfl ?_
            intro P hP
            rw [h3all P]
      _ = Nat.card (Sylow 3 X) * 8 := by simp [Finset.sum_const, Nat.card_eq_fintype_card]
      _ = n3 * 8 := by rfl
  have hs5 : (∑ P : Sylow 5 X, (Nat.card (P : Subgroup X) - 1)) = n5 * 4 := by
    calc
      (∑ P : Sylow 5 X, (Nat.card (P : Subgroup X) - 1))
          = ∑ P : Sylow 5 X, 4 := by
            refine Finset.sum_congr rfl ?_
            intro P hP
            rw [h5all P]
      _ = Nat.card (Sylow 5 X) * 4 := by simp [Finset.sum_const, Nat.card_eq_fintype_card]
      _ = n5 * 4 := by rfl
  have hs7 : (∑ P : Sylow 7 X, (Nat.card (P : Subgroup X) - 1)) = n7 * 6 := by
    calc
      (∑ P : Sylow 7 X, (Nat.card (P : Subgroup X) - 1))
          = ∑ P : Sylow 7 X, 6 := by
            refine Finset.sum_congr rfl ?_
            intro P hP
            rw [h7all P]
      _ = Nat.card (Sylow 7 X) * 6 := by simp [Finset.sum_const, Nat.card_eq_fintype_card]
      _ = n7 * 6 := by rfl
  rw [hX, hs3, hs5, hs7] at hle
  nlinarith


public theorem aSeven_odd_subgroup_card_le_21
    (X : Subgroup (alternatingGroup (Fin 7))) (hodd : Odd (Nat.card X)) :
    Nat.card X ≤ 21 := by
  classical
  let n : ℕ := Nat.card X
  have hA7card : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    decide
  have hdvd2520 : n ∣ 2520 := by
    dsimp [n]
    have h := Subgroup.card_subgroup_dvd_card X
    rw [hA7card] at h
    exact h
  have h2 : ¬ 2 ∣ n := by
    exact hodd.not_two_dvd_nat
  have hcop8 : Nat.Coprime n 8 := by
    simpa using (Nat.prime_two.coprime_pow_of_not_dvd (m := 3) h2)
  have h315 : n ∣ 315 := by
    rw [show (2520 : ℕ) = 8 * 315 by norm_num] at hdvd2520
    exact (hcop8.dvd_mul_left).mp hdvd2520
  have hcases : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 9 ∨ n = 15 ∨ n = 21 ∨
      n = 35 ∨ n = 45 ∨ n = 63 ∨ n = 105 ∨ n = 315 := odd_divisor_315_cases h315 hodd
  rcases hcases with h1 | h3 | h5 | h7 | h9 | h15 | h21 | h35 | h45 | h63 | h105 | h315
  all_goals try omega
  · exfalso
    exact card_not_35 X (by simpa [n] using h35)
  · exfalso
    exact card_not_45 X (by simpa [n] using h45)
  · exfalso
    exact card_not_63 X (by simpa [n] using h63)
  · exfalso
    exact card_not_105 X (by simpa [n] using h105)
  · exfalso
    exact card_not_315 X (by simpa [n] using h315)

end CFSG.GorensteinWalter
