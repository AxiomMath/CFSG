module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KG

open Subgroup

theorem perm_seven_orderOf_ne_fifteen (σ : Equiv.Perm (Fin 7)) : orderOf σ ≠ 15 := by
  intro h
  have hlcm := σ.lcm_cycleType
  have hsum : σ.cycleType.sum ≤ 7 := by
    rw [σ.sum_cycleType]
    simpa using Finset.card_le_univ σ.support
  have hmem : ∀ c ∈ σ.cycleType, c = 3 ∨ c = 5 := by
    intro c hc
    have h1 : c ∣ 15 := h ▸ σ.dvd_of_mem_cycleType hc
    have h2 : c ≤ 7 := (Multiset.le_sum_of_mem hc).trans hsum
    have h3 := σ.two_le_of_mem_cycleType hc
    interval_cases c <;> simp_all
  have h3 : 3 ∈ σ.cycleType := by
    by_contra h3
    have : σ.cycleType.lcm ∣ 5 := Multiset.lcm_dvd.mpr fun c hc => by
      rcases hmem c hc with rfl | rfl
      · exact absurd hc h3
      · exact dvd_rfl
    rw [hlcm, h] at this
    norm_num at this
  have h5 : 5 ∈ σ.cycleType := by
    by_contra h5
    have : σ.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.mpr fun c hc => by
      rcases hmem c hc with rfl | rfl
      · exact dvd_rfl
      · exact absurd hc h5
    rw [hlcm, h] at this
    norm_num at this
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem h3
  rw [ht] at h5 hsum
  rw [Multiset.sum_cons] at hsum
  have h5' : 5 ∈ t := (Multiset.mem_cons.mp h5).resolve_left (by norm_num)
  have := Multiset.le_sum_of_mem h5'
  omega

variable {X : Type*} [Group X]

theorem conj_pow_iterate {x c : X} {k : ℕ} (hk : x * c * x⁻¹ = c ^ k) (m : ℕ) :
    x ^ m * c * (x ^ m)⁻¹ = c ^ k ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc x ^ (m + 1) * c * (x ^ (m + 1))⁻¹ = x ^ m * (x * c * x⁻¹) * (x ^ m)⁻¹ := by group
      _ = (x ^ m * c * (x ^ m)⁻¹) ^ k := by rw [hk, conj_pow]
      _ = c ^ k ^ (m + 1) := by rw [ih, ← pow_mul, pow_succ]

theorem commute_of_conj_mem_zpowers_five [Finite X] {x c : X} (hx3 : x ^ 3 = 1)
    (hc5 : orderOf c = 5) (h : x * c * x⁻¹ ∈ zpowers c) : Commute x c := by
  have : Finite (zpowers c) := inferInstance
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).mpr h
  have hk' : c ^ k = x * c * x⁻¹ := hk
  have h3 := conj_pow_iterate hk'.symm 3
  rw [hx3, one_mul, inv_one, mul_one] at h3
  have hmod : k ^ 3 % 5 = 1 := by
    have h' : c ^ k ^ 3 = c ^ 1 := by rw [← h3, pow_one]
    have := (pow_eq_pow_iff_modEq.mp h')
    rw [hc5] at this
    exact this
  have hk1 : k % 5 = 1 := by
    have : k ^ 3 % 5 = (k % 5) ^ 3 % 5 := Nat.pow_mod k 3 5
    have hlt : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : k % 5 <;> omega
  have hck : c ^ k = c := by
    rw [← pow_mod_orderOf, hc5, hk1, pow_one]
  change x * c = c * x
  calc x * c = x * c * x⁻¹ * x := by group
    _ = c * x := by rw [← hk', hck]

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KG
