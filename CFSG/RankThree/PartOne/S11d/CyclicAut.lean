module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartOne

open Subgroup

theorem dvd_sub_one_of_dvd_pow_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℤ} {n : ℕ}
    (h : (p : ℤ) ^ n ∣ k ^ p - 1) : (p : ℤ) ^ (n - 1) ∣ k - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Fact p.Prime := ⟨hp⟩
  have hpd : (p : ℤ) ∣ k ^ p - 1 := (dvd_pow_self (p : ℤ) hn.ne').trans h
  have hpk : (p : ℤ) ∣ k - 1 := by
    have h1 : ((k ^ p - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpd
    have h2 : ((k - 1 : ℤ) : ZMod p) = 0 := by
      push_cast at h1 ⊢
      rwa [ZMod.pow_card] at h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h2
  by_cases hk1 : k - 1 = 0
  · rw [hk1]
    exact dvd_zero _
  have hpk' : ¬ (p : ℤ) ∣ k := by
    intro hk
    have : (p : ℤ) ∣ 1 := by
      have := dvd_sub hk hpk
      simpa using this
    have := Int.eq_one_of_dvd_one (by positivity) this
    exact hp.one_lt.ne' (by exact_mod_cast this)
  have hlte := Int.emultiplicity_pow_sub_pow hp hodd (x := k) (y := 1) (by simpa using hpk) hpk' p
  rw [one_pow] at hlte
  have hle : (n : ℕ∞) ≤ emultiplicity (p : ℤ) (k ^ p - 1) := (pow_dvd_iff_le_emultiplicity).mp h
  rw [hlte, hp.emultiplicity_self] at hle
  rw [pow_dvd_iff_le_emultiplicity]
  generalize emultiplicity (p : ℤ) (k - 1) = e at hle ⊢
  induction e using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    have : n ≤ m + 1 := by exact_mod_cast hle
    exact_mod_cast (by omega : n - 1 ≤ m)

variable {G : Type*} [Group G]

theorem pow_conj_eq_zpow {a s : G} {k : ℤ} (h : a * s * a⁻¹ = s ^ k) (j : ℕ) :
    a ^ j * s * (a ^ j)⁻¹ = s ^ (k ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc a ^ (j + 1) * s * (a ^ (j + 1))⁻¹ = a * (a ^ j * s * (a ^ j)⁻¹) * a⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          group
      _ = a * s ^ (k ^ j) * a⁻¹ := by rw [ih]
      _ = (a * s * a⁻¹) ^ (k ^ j) := by rw [conj_zpow]
      _ = s ^ (k * k ^ j) := by rw [h, ← zpow_mul]
      _ = s ^ (k ^ (j + 1)) := by rw [pow_succ']

theorem conj_pow_eq_of_cyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup G}
    (hS : IsCyclic S) (hSp : IsPGroup p S) {a : G} (ha : a ∈ normalizer (S : Set G))
    (hap : a ^ p = 1) (t : G) (ht : t ∈ S) : a * t ^ p * a⁻¹ = t ^ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hS.exists_generator
  set s : G := (g : G) with hsdef
  have hsS : s ∈ S := g.2
  have hmem : ∀ x ∈ S, ∃ m : ℤ, x = s ^ m := by
    intro x hx
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    refine ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    simpa [hsdef] using this.symm
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hSp) g
  have hns : orderOf s = p ^ n := by rw [hsdef, Subgroup.orderOf_coe]; exact hn
  have haS : a * s * a⁻¹ ∈ S := (mem_normalizer_iff.mp ha s).mp hsS
  obtain ⟨k, hk⟩ := hmem _ haS
  have hkp := pow_conj_eq_zpow hk p
  rw [hap, inv_one, mul_one, one_mul] at hkp
  have h1 : s ^ (k ^ p - 1) = 1 := by
    rw [zpow_sub, zpow_one, ← hkp, mul_inv_cancel]
  have h2 : (p : ℤ) ^ n ∣ k ^ p - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hns] at this
    exact_mod_cast this
  have h3 := dvd_sub_one_of_dvd_pow_sub_one hp hp2 h2
  obtain ⟨m, hm⟩ := hmem t ht
  have hconj : a * t ^ p * a⁻¹ = s ^ (k * (m * p)) := by
    rw [hm, ← zpow_natCast, ← zpow_mul, ← conj_zpow, hk, ← zpow_mul]
  have hexp : (p : ℤ) ^ n ∣ (k - 1) * (m * p) := by
    rcases n with _ | n
    · simp
    · have h5 : (p : ℤ) ^ n * p ∣ (k - 1) * p := mul_dvd_mul h3 (dvd_refl _)
      rw [pow_succ]
      calc (p : ℤ) ^ n * p ∣ (k - 1) * p := h5
        _ ∣ (k - 1) * (m * p) := by
          rw [show (k - 1) * (m * p) = (k - 1) * p * m by ring]
          exact dvd_mul_right _ _
  have hone : s ^ ((k - 1) * (m * p)) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hns]
    exact_mod_cast hexp
  rw [hconj, hm, ← zpow_natCast, ← zpow_mul]
  have : s ^ (k * (m * p)) = s ^ ((k - 1) * (m * p)) * s ^ (m * (p : ℕ)) := by
    rw [← zpow_add]
    congr 1
    ring
  rw [this, hone, one_mul]

theorem zpowers_eq_of_conj_ne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup G}
    (hS : IsCyclic S) (hSp : IsPGroup p S) {a : G} (ha : a ∈ normalizer (S : Set G))
    (hap : a ^ p = 1) {y : G} (hy : y ∈ S) (hmove : a * y * a⁻¹ ≠ y) : zpowers y = S := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hS.exists_generator
  set s : G := (g : G) with hsdef
  have hmem : ∀ x ∈ S, ∃ m : ℤ, x = s ^ m := by
    intro x hx
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    refine ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    simpa [hsdef] using this.symm
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hSp) g
  have hns : orderOf s = p ^ n := by rw [hsdef, Subgroup.orderOf_coe]; exact hn
  have hsS : s ∈ S := g.2
  obtain ⟨m, hm⟩ := hmem y hy
  refine le_antisymm (zpowers_le.mpr hy) ?_
  by_cases hpm : (p : ℤ) ∣ m
  · exfalso
    obtain ⟨m', rfl⟩ := hpm
    apply hmove
    have hy' : y = (s ^ m') ^ p := by
      rw [hm, ← zpow_natCast, ← zpow_mul, mul_comm]
    rw [hy']
    exact conj_pow_eq_of_cyclic hp hp2 hS hSp ha hap _ (zpow_mem hsS m')
  · have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have h1 : IsCoprime (p : ℤ) m := (Irreducible.coprime_iff_not_dvd hpz.irreducible).mpr hpm
    obtain ⟨u, v, huv⟩ := h1.pow_left (m := n)
    have hsn : s ^ ((p : ℤ) ^ n) = 1 := by
      have h := pow_orderOf_eq_one s
      rw [hns] at h
      have h' : ((p : ℤ) ^ n) = ((p ^ n : ℕ) : ℤ) := by push_cast; rfl
      rw [h', zpow_natCast]
      exact h
    have hsy : s = y ^ v := by
      have huv' : (p : ℤ) ^ n * u + m * v = 1 := by linarith [huv]
      calc s = s ^ ((p : ℤ) ^ n * u + m * v) := by rw [huv', zpow_one]
        _ = (s ^ ((p : ℤ) ^ n)) ^ u * (s ^ m) ^ v := by rw [zpow_add, zpow_mul, zpow_mul]
        _ = y ^ v := by rw [hsn, one_zpow, one_mul, ← hm]
    intro x hx
    obtain ⟨j, rfl⟩ := hmem x hx
    rw [hsy, ← zpow_mul]
    exact zpow_mem (mem_zpowers y) _

end CFSG.RankThree.PartOne
