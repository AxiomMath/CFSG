module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup

private theorem k91par_orderOf {K : Type*} [Group K] {n : ℕ} {z : K}
    (hz : center K = zpowers z) (hZ : Nat.card (center K) = n) : orderOf z = n := by
  rw [← Nat.card_zpowers, ← hz, hZ]

private theorem k91par_mem {K : Type*} [Group K] {n : ℕ} (hn : n = 3 ∨ n = 6) {z : K}
    (hz : center K = zpowers z) (hZ : Nat.card (center K) = n) {c : K} (hc : c ∈ center K) :
    ∃ m < n, c = z ^ m := by
  classical
  have ho := k91par_orderOf hz hZ
  have hfin : IsOfFinOrder z := orderOf_pos_iff.1 (by omega)
  rw [hz, hfin.mem_zpowers_iff_mem_range_orderOf] at hc
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hc
  exact ⟨m, by simpa [ho] using hm, rfl⟩

private theorem k91par_ninth {K : Type*} [Group K] {n : ℕ} (hn : n = 3 ∨ n = 6) {z : K}
    (hzn : z ^ n = 1) (m : ℕ) : ∃ i < 2, (n = 3 → i = 0) ∧ (z ^ m) ^ 9 = z ^ (3 * i) := by
  rcases hn with rfl | rfl
  · refine ⟨0, by norm_num, fun _ => rfl, ?_⟩
    rw [← pow_mul, pow_eq_pow_mod _ hzn]
    simp [Nat.mul_mod]
  · refine ⟨m % 2, Nat.mod_lt _ (by norm_num), fun h => absurd h (by norm_num), ?_⟩
    rw [← pow_mul, pow_eq_pow_mod _ hzn, pow_eq_pow_mod (3 * (m % 2)) hzn]
    congr 1
    omega

theorem exists_cover_params {K : Type*} [Group K] {n : ℕ} (hn : n = 3 ∨ n = 6) {z : K}
    (hz : center K = zpowers z) (hZ : Nat.card (center K) = n) {x y : K}
    (hx : x ^ 2 ∈ center K) (hy : y ^ 4 ∈ center K) (hxy : (x * y) ^ 5 ∈ center K)
    (hxyy : (x * y * y) ^ 5 ∈ center K) :
    ∃ i j k l : ℕ, (n = 3 → i = 0 ∧ j = 0) ∧ i < 2 ∧ j < 2 ∧ k < n ∧ l < n ∧
      (x ^ 9) ^ 2 = z ^ (3 * i) ∧ (y ^ 9) ^ 4 = z ^ (3 * j) ∧ (x ^ 9 * y ^ 9) ^ 5 = z ^ k ∧
      (x ^ 9 * y ^ 9 * y ^ 9) ^ 5 = z ^ l := by
  have hzn : z ^ n = 1 := k91par_orderOf hz hZ ▸ pow_orderOf_eq_one z
  have hu : (x ^ 2) ^ 4 ∈ center K := pow_mem hx 4
  have hv : (y ^ 4) ^ 2 ∈ center K := pow_mem hy 2
  have huv : (x ^ 2) ^ 4 * (y ^ 4) ^ 2 ∈ center K := mul_mem hu hv
  have huvv : (x ^ 2) ^ 4 * (y ^ 4) ^ 2 * (y ^ 4) ^ 2 ∈ center K := mul_mem huv hv
  have hcomm : ∀ {c : K}, c ∈ center K → ∀ g : K, Commute g c := fun hc g => mem_center_iff.1 hc g
  have hx9 : x ^ 9 = x * (x ^ 2) ^ 4 := by rw [← pow_mul, ← pow_succ']
  have hy9 : y ^ 9 = y * (y ^ 4) ^ 2 := by rw [← pow_mul, ← pow_succ']
  have hxy9 : x ^ 9 * y ^ 9 = x * y * ((x ^ 2) ^ 4 * (y ^ 4) ^ 2) := by
    rw [hx9, hy9]
    exact (hcomm hu y).symm.mul_mul_mul_comm x _
  have hxyy9 : x ^ 9 * y ^ 9 * y ^ 9 = x * y * y * ((x ^ 2) ^ 4 * (y ^ 4) ^ 2 * (y ^ 4) ^ 2) := by
    rw [hxy9, hy9]
    exact (hcomm huv y).symm.mul_mul_mul_comm (x * y) _
  have hk : (x ^ 9 * y ^ 9) ^ 5 ∈ center K := by
    rw [hxy9, (hcomm huv (x * y)).mul_pow]
    exact mul_mem hxy (pow_mem huv 5)
  have hl : (x ^ 9 * y ^ 9 * y ^ 9) ^ 5 ∈ center K := by
    rw [hxyy9, (hcomm huvv (x * y * y)).mul_pow]
    exact mul_mem hxyy (pow_mem huvv 5)
  obtain ⟨k, hkn, hk⟩ := k91par_mem hn hz hZ hk
  obtain ⟨l, hln, hl⟩ := k91par_mem hn hz hZ hl
  obtain ⟨m, -, hm⟩ := k91par_mem hn hz hZ hx
  obtain ⟨m', -, hm'⟩ := k91par_mem hn hz hZ hy
  obtain ⟨i, hi2, hi3, hi⟩ := k91par_ninth hn hzn m
  obtain ⟨j, hj2, hj3, hj⟩ := k91par_ninth hn hzn m'
  exact ⟨i, j, k, l, fun h3 => ⟨hi3 h3, hj3 h3⟩, hi2, hj2, hkn, hln,
    by rw [pow_right_comm, hm, hi], by rw [pow_right_comm, hm', hj], hk, hl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
