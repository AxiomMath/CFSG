module

import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.Quasithin.Fan86

open Subgroup

theorem commute_of_pow_four {A : Type*} [Group A] {x g : A} {p : ℕ} (hp : Odd p) (hx : x ^ p = 1)
    (hg : g ^ 4 = 1) (h : x * g * x⁻¹ ∈ Subgroup.zpowers g) : x * g = g * x := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h
  have hmod : g ^ m = g ^ (m % 4) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod m 4]
    rw [zpow_add, zpow_mul, show g ^ (4 : ℤ) = 1 by exact_mod_cast hg, one_zpow, one_mul]
  have hcases : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  have hconj : ∀ y : A, x * (y * g * y⁻¹) * x⁻¹ = (x * y) * g * (x * y)⁻¹ := fun y => by group
  have hone : ∀ y : A, y * g * y⁻¹ = 1 → g = 1 := fun y hy => by
    calc g = y⁻¹ * (y * g * y⁻¹) * y := by group
      _ = 1 := by rw [hy]; group
  rcases hcases with h0 | h1 | h2 | h3
  · rw [h0] at hmod
    have : x * g * x⁻¹ = 1 := by rw [← hm, hmod]; simp
    rw [hone x this]
    simp
  · rw [h1] at hmod
    have : x * g * x⁻¹ = g := by rw [← hm, hmod]; simp
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  · rw [h2] at hmod
    have hxg : x * g * x⁻¹ = g ^ 2 := by rw [← hm, hmod]; simp
    have : x * x * g * (x * x)⁻¹ = 1 := by
      calc x * x * g * (x * x)⁻¹ = x * (x * g * x⁻¹) * x⁻¹ := by group
        _ = x * g ^ 2 * x⁻¹ := by rw [hxg]
        _ = (x * g * x⁻¹) ^ 2 := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hxg, ← pow_mul]; simpa using hg
    rw [hone (x * x) this]
    simp
  · rw [h3] at hmod
    have hxg : x * g * x⁻¹ = g⁻¹ := by
      rw [← hm, hmod]
      have : g ^ (3 : ℤ) * g = 1 := by
        rw [← zpow_add_one]
        simpa using hg
      exact eq_inv_of_mul_eq_one_left this
    have h2 : (x ^ 2) * g = g * (x ^ 2) := by
      have : x * x * g * (x * x)⁻¹ = g := by
        calc x * x * g * (x * x)⁻¹ = x * (x * g * x⁻¹) * x⁻¹ := by group
          _ = x * g⁻¹ * x⁻¹ := by rw [hxg]
          _ = (x * g * x⁻¹)⁻¹ := by group
          _ = g := by rw [hxg, inv_inv]
      rw [mul_inv_eq_iff_eq_mul] at this
      rw [pow_two]
      exact this
    obtain ⟨q, rfl⟩ := hp
    have hxq : x = (x ^ 2) ^ (q + 1) := by
      rw [← pow_mul]
      calc x = x ^ (2 * q + 1) * x := by rw [hx]; simp
        _ = x ^ (2 * (q + 1)) := by rw [← pow_succ]; ring_nf
    have hc : Commute (x ^ 2) g := h2
    have := (hc.pow_left (q + 1)).eq
    rw [← hxq] at this
    exact this

theorem comm_mod_of_cyclic_four {G : Type*} [Group G] (N S : Subgroup G)
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) {x : G}
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) (hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S) {p : ℕ}
    (hp : Odd p) (hxp : x ^ p = 1) {g : G} (hgS : g ∈ S) (hg4 : g ^ 4 ∈ N)
    (hgen : ∀ s ∈ S, ∃ n : ℤ, g ^ n * s⁻¹ ∈ N) : ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ N := by
  have hnorm : (N.subgroupOf (Subgroup.normalizer (N : Set G))).Normal := inferInstance
  set A := Subgroup.normalizer (N : Set G) with hA
  let π : ↥A →* (↥A ⧸ N.subgroupOf A) := QuotientGroup.mk' (N.subgroupOf A)
  have hπ : ∀ a : ↥A, π a = 1 ↔ (a : G) ∈ N := fun a => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let x' : ↥A := ⟨x, hxN⟩
  let g' : ↥A := ⟨g, hSN hgS⟩
  have hx1 : π x' ^ p = 1 := by
    rw [← map_pow, hπ]
    show x ^ p ∈ N
    rw [hxp]; exact N.one_mem
  have hg1 : π g' ^ 4 = 1 := by
    rw [← map_pow, hπ]
    exact hg4
  have hmem : ∀ s : G, (hs : s ∈ S) → ∀ n : ℤ, g ^ n * s⁻¹ ∈ N →
      π ⟨s, hSN hs⟩ = π g' ^ n := by
    intro s hs n hn
    have : π (g' ^ n * ⟨s, hSN hs⟩⁻¹) = 1 := by
      rw [hπ]
      exact hn
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at this
    exact this.symm
  have hconj : π x' * π g' * (π x')⁻¹ ∈ Subgroup.zpowers (π g') := by
    obtain ⟨n, hn⟩ := hgen _ (hxS g hgS)
    have h := hmem _ (hxS g hgS) n hn
    have : π x' * π g' * (π x')⁻¹ = π ⟨x * g * x⁻¹, hSN (hxS g hgS)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this, h]
    exact Subgroup.zpow_mem_zpowers _ _
  have hcomm := commute_of_pow_four hp hx1 hg1 hconj
  intro s hs
  obtain ⟨n, hn⟩ := hgen s hs
  have h := hmem s hs n hn
  have hs1 : π x' * π ⟨s, hSN hs⟩ = π ⟨s, hSN hs⟩ * π x' := by
    rw [h]
    exact ((Commute.zpow_right (show Commute (π x') (π g') from hcomm) n)).eq
  have : π (x' * ⟨s, hSN hs⟩ * x'⁻¹ * ⟨s, hSN hs⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hs1]
    group
  rw [hπ] at this
  exact this

theorem mem_of_commute_mod {G : Type*} [Group G] (N : Subgroup G) {x k : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) (hk : k ∈ Subgroup.normalizer (N : Set G))
    {p : ℕ} (hp : Odd p) (hxp : x ^ p = 1) {i m : ℕ} (hk2 : k ^ (2 ^ m) = 1)
    (hcomm : x * k * x⁻¹ * k⁻¹ ∈ N) (hxk : (x ^ i * k) ^ p ∈ N) : k ∈ N := by
  have hnorm : (N.subgroupOf (Subgroup.normalizer (N : Set G))).Normal := inferInstance
  set A := Subgroup.normalizer (N : Set G) with hA
  let π : ↥A →* (↥A ⧸ N.subgroupOf A) := QuotientGroup.mk' (N.subgroupOf A)
  have hπ : ∀ a : ↥A, π a = 1 ↔ (a : G) ∈ N := fun a => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let x' : ↥A := ⟨x, hx⟩
  let k' : ↥A := ⟨k, hk⟩
  have hx1 : π x' ^ p = 1 := by
    rw [← map_pow, hπ]
    show x ^ p ∈ N
    rw [hxp]; exact N.one_mem
  have hk1 : π k' ^ (2 ^ m) = 1 := by
    rw [← map_pow, hπ]
    show k ^ (2 ^ m) ∈ N
    rw [hk2]; exact N.one_mem
  have hc : Commute (π x') (π k') := by
    have : π (x' * k' * x'⁻¹ * k'⁻¹) = 1 := by
      rw [hπ]
      exact hcomm
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      at this
    exact this
  have hxk' : (π x' ^ i * π k') ^ p = 1 := by
    have : π ((x' ^ i * k') ^ p) = 1 := by
      rw [hπ]
      exact hxk
    simpa [map_pow, map_mul] using this
  rw [(hc.pow_left i).mul_pow, ← pow_mul, mul_comm i p, pow_mul, hx1, one_pow, one_mul] at hxk'
  have hcop : Nat.Coprime p (2 ^ m) := Nat.Coprime.pow_right m (Nat.coprime_two_right.2 hp)
  have : π k' ^ Nat.gcd p (2 ^ m) = 1 := pow_gcd_eq_one.2 ⟨hxk', hk1⟩
  rw [hcop.gcd_eq_one, pow_one] at this
  exact (hπ k').1 this

theorem comm_eq_one_of_central {G : Type*} [Group G] {x s : G} {p m : ℕ} (hp : Odd p)
    (hxp : x ^ p = 1) (hxl : x * (x * s * x⁻¹ * s⁻¹) * x⁻¹ = x * s * x⁻¹ * s⁻¹)
    (hl2 : (x * s * x⁻¹ * s⁻¹) ^ (2 ^ m) = 1) : x * s * x⁻¹ * s⁻¹ = 1 := by
  set l := x * s * x⁻¹ * s⁻¹ with hl
  have hxs : x * s * x⁻¹ = l * s := by rw [hl]; group
  have key : ∀ j : ℕ, x ^ j * s * (x ^ j)⁻¹ = l ^ j * s := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : x ^ (j + 1) * s * (x ^ (j + 1))⁻¹ = x * (x ^ j * s * (x ^ j)⁻¹) * x⁻¹ := by group
      rw [e, ih]
      calc x * (l ^ j * s) * x⁻¹ = (x * l ^ j * x⁻¹) * (x * s * x⁻¹) := by group
        _ = (x * l * x⁻¹) ^ j * (x * s * x⁻¹) := by rw [conj_pow]
        _ = l ^ j * (l * s) := by rw [hxl, hxs]
        _ = l ^ (j + 1) * s := by group
  have h1 : l ^ p * s = 1 * s := by
    rw [← key p, hxp]
    simp
  have h2 : l ^ p = 1 := mul_right_cancel h1
  have hcop : Nat.Coprime p (2 ^ m) := Nat.Coprime.pow_right m (Nat.coprime_two_right.2 hp)
  have := pow_gcd_eq_one.2 ⟨h2, hl2⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

end CFSG.Quasithin.Fan86
