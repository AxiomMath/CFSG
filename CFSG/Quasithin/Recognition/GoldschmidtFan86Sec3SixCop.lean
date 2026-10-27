module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.Quasithin.Fan86

open Subgroup

theorem comm_mem_of_cyclic_gen {G : Type*} [Group G] (N S : Subgroup G)
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) {g : G} (hgS : g ∈ S)
    (hgen : ∀ s ∈ S, ∃ n : ℤ, g ^ n * s⁻¹ ∈ N) :
    ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ N := by
  have hnorm : (N.subgroupOf (Subgroup.normalizer (N : Set G))).Normal := inferInstance
  set A := Subgroup.normalizer (N : Set G) with hA
  let π : ↥A →* (↥A ⧸ N.subgroupOf A) := QuotientGroup.mk' (N.subgroupOf A)
  have hπ : ∀ a : ↥A, π a = 1 ↔ (a : G) ∈ N := fun a => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hmem : ∀ s : G, (hs : s ∈ S) → ∃ n : ℤ, π ⟨s, hSN hs⟩ = π ⟨g, hSN hgS⟩ ^ n := by
    intro s hs
    obtain ⟨n, hn⟩ := hgen s hs
    refine ⟨n, ?_⟩
    have : π (⟨g, hSN hgS⟩ ^ n * ⟨s, hSN hs⟩⁻¹) = 1 := by
      rw [hπ]
      exact hn
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at this
    exact this.symm
  intro s hs t ht
  obtain ⟨n, hn⟩ := hmem s hs
  obtain ⟨m, hm⟩ := hmem t ht
  have hcomm : π ⟨s, hSN hs⟩ * π ⟨t, hSN ht⟩ = π ⟨t, hSN ht⟩ * π ⟨s, hSN hs⟩ := by
    rw [hn, hm, ← zpow_add, ← zpow_add, add_comm]
  have : π (⟨s, hSN hs⟩ * ⟨t, hSN ht⟩ * ⟨s, hSN hs⟩⁻¹ * ⟨t, hSN ht⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  rw [hπ] at this
  exact this

theorem commute_of_pow_commute {A : Type*} [Group A] {x s : A} {p d : ℕ} (hp : p.Prime)
    (hxp : x ^ p = 1) (hd0 : 0 < d) (hdp : d < p) (h : Commute (x ^ d) s) : Commute x s := by
  have hcop : Nat.gcd d p = 1 :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hd0 hdp))
  have hbez := Nat.gcd_eq_gcd_ab d p
  rw [hcop] at hbez
  have hx : x = (x ^ d) ^ (Nat.gcdA d p) := by
    calc x = x ^ (1 : ℤ) := (zpow_one x).symm
      _ = x ^ ((d : ℤ) * Nat.gcdA d p + (p : ℤ) * Nat.gcdB d p) := by
        rw [← hbez]
        rfl
      _ = (x ^ d) ^ (Nat.gcdA d p) := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hxp, one_zpow, mul_one]
  rw [hx]
  exact h.zpow_left _

theorem comm_mod_of_relIndex_lt {G : Type*} [Group G] (U S : Subgroup G)
    (hSN : S ≤ Subgroup.normalizer (U : Set G)) {x : G}
    (hxN : x ∈ Subgroup.normalizer (U : Set G)) (hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S) {p : ℕ}
    (hp : p.Prime) (hxp : x ^ p = 1) (hlt : U.relIndex S < p) (hfin : U.relIndex S ≠ 0) :
    ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ U := by
  have hnorm : (U.subgroupOf (Subgroup.normalizer (U : Set G))).Normal := inferInstance
  set A := Subgroup.normalizer (U : Set G) with hA
  let π : ↥A →* (↥A ⧸ U.subgroupOf A) := QuotientGroup.mk' (U.subgroupOf A)
  have hπ : ∀ a : ↥A, π a = 1 ↔ (a : G) ∈ U := fun a => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcard : Nat.card ((S.subgroupOf A).map π) = U.relIndex S := by
    have h1 := Subgroup.relIndex_ker (S.subgroupOf A) π
    have hker : π.ker = U.subgroupOf A := QuotientGroup.ker_mk' _
    rw [hker, Subgroup.relIndex_subgroupOf hSN] at h1
    exact h1.symm
  have hxS' : ∀ (j : ℕ) (s : G), s ∈ S → x ^ j * s * (x ^ j)⁻¹ ∈ S := by
    intro j
    induction j with
    | zero => intro s hs; simpa using hs
    | succ j ih =>
      intro s hs
      have e : x ^ (j + 1) * s * (x ^ (j + 1))⁻¹ = x ^ j * (x * s * x⁻¹) * (x ^ j)⁻¹ := by group
      rw [e]
      exact ih _ (hxS s hs)
  intro s hs
  let x' : ↥A := ⟨x, hxN⟩
  let s' : ↥A := ⟨s, hSN hs⟩
  let g : ℕ → (↥A ⧸ U.subgroupOf A) := fun n => π x' ^ n * π s' * (π x' ^ n)⁻¹
  have hg : ∀ n : ℕ, π (x' ^ n * s' * (x' ^ n)⁻¹) = g n := by
    intro n
    simp [g, map_mul, map_pow, map_inv]
  let f : Fin p → ↥((S.subgroupOf A).map π) := fun j =>
    ⟨g j, ⟨x' ^ (j : ℕ) * s' * (x' ^ (j : ℕ))⁻¹, by
      show x ^ (j : ℕ) * s * (x ^ (j : ℕ))⁻¹ ∈ S
      exact hxS' _ s hs, hg j⟩⟩
  have hlt' : Nat.card ↥((S.subgroupOf A).map π) < Fintype.card (Fin p) := by
    rw [hcard, Fintype.card_fin]
    exact hlt
  have hfinS : Finite ↥((S.subgroupOf A).map π) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hfin)
  have : Fintype ↥((S.subgroupOf A).map π) := Fintype.ofFinite _
  have hlt'' : Fintype.card ↥((S.subgroupOf A).map π) < Fintype.card (Fin p) := by
    rw [← Nat.card_eq_fintype_card]
    exact hlt'
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt''
  have hx1 : π x' ^ p = 1 := by
    rw [← map_pow]
    have : x' ^ p = 1 := Subtype.ext (by simpa using hxp)
    rw [this, map_one]
  have key : ∀ i j : Fin p, (i : ℕ) < j → g i = g j → Commute (π x') (π s') := by
    intro i j hlt hgij
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (j : ℕ) = i + d := ⟨j - i, by omega⟩
    have e : π x' ^ (i : ℕ) * π s' * (π x' ^ (i : ℕ))⁻¹ =
        π x' ^ (i : ℕ) * (π x' ^ d * π s' * (π x' ^ d)⁻¹) * (π x' ^ (i : ℕ))⁻¹ := by
      have h1 : g i = g j := hgij
      simp only [g, hd, pow_add] at h1
      rw [h1]
      group
    have e2 : π s' = π x' ^ d * π s' * (π x' ^ d)⁻¹ :=
      mul_left_cancel (mul_right_cancel e)
    have hcomm : Commute (π x' ^ d) (π s') := by
      have := mul_inv_eq_iff_eq_mul.1 e2.symm
      exact this
    exact commute_of_pow_commute hp hx1 (by omega) (by omega) hcomm
  have hcomm : Commute (π x') (π s') := by
    rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h) : (i : ℕ) ≠ j) with h | h
    · exact key i j h (congrArg Subtype.val hfij)
    · exact key j i h (congrArg Subtype.val hfij).symm
  have : π (x' * s' * x'⁻¹ * s'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm.eq]
    group
  rw [hπ] at this
  exact this

theorem eq_of_relIndex_le_two {G : Type*} [Group G] {M N D : Subgroup G} (hMN : M ≤ N)
    (hND : N ≤ D) (hle : M.relIndex D ≤ 2) (hfin : M.relIndex D ≠ 0) (hne : N ≠ D) : N ≤ M := by
  have h := Subgroup.relIndex_mul_relIndex M N D hMN hND
  have hN : N.relIndex D ≠ 1 := fun h1 => hne (le_antisymm hND (Subgroup.relIndex_eq_one.1 h1))
  have hN0 : N.relIndex D ≠ 0 := fun h0 => hfin (by rw [← h, h0, mul_zero])
  have hN2 : 2 ≤ N.relIndex D := by omega
  have hM1 : M.relIndex N = 1 := by
    have : M.relIndex N * N.relIndex D ≤ 2 := h ▸ hle
    have hM0 : M.relIndex N ≠ 0 := fun h0 => hfin (by rw [← h, h0, zero_mul])
    by_contra hne1
    have h2 : 2 ≤ M.relIndex N := by omega
    have h4 : 2 * 2 ≤ M.relIndex N * N.relIndex D := Nat.mul_le_mul h2 hN2
    omega
  exact Subgroup.relIndex_eq_one.1 hM1

end CFSG.Quasithin.Fan86
