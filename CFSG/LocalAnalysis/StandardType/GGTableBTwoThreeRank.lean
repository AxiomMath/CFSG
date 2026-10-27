module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.StandardType.TwoThree

open Module

section Basic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def fixG (U : Submodule K V) : Subgroup (Module.End K V)ˣ where
  carrier := {g | ∀ u ∈ U, (g : Module.End K V) u = u}
  mul_mem' {a b} ha hb u hu := by
    change ((a * b : (Module.End K V)ˣ) : Module.End K V) u = u
    rw [Units.val_mul, Module.End.mul_apply, hb u hu, ha u hu]
  one_mem' u _ := rfl
  inv_mem' {a} ha u hu := by
    change ((a⁻¹ : (Module.End K V)ˣ) : Module.End K V) u = u
    conv_lhs => rw [← ha u hu]
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]

theorem mem_fixG {U : Submodule K V} {g : (Module.End K V)ˣ} :
    g ∈ fixG U ↔ ∀ u ∈ U, (g : Module.End K V) u = u :=
  Iff.rfl

theorem fixG_top : fixG (⊤ : Submodule K V) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply Units.ext
  apply LinearMap.ext
  intro v
  exact hg v Submodule.mem_top

theorem fixG_inf_le {U₁ U₂ U : Submodule K V} (hU : U ≤ U₁ ⊔ U₂) :
    fixG U₁ ⊓ fixG U₂ ≤ fixG U := by
  rintro g ⟨h1, h2⟩ u hu
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hU hu)
  rw [map_add, h1 a ha, h2 b hb]

theorem sum_apply_eq_zero {x : Module.End K V} (hx3 : x ^ 3 = 1) {U : Submodule K V}
    (hxU : ∀ u ∈ U, x u ∈ U) (hfp : ∀ u ∈ U, x u = u → u = 0) {w : V} (hw : w ∈ U) :
    (1 + x + x ^ 2 : Module.End K V) w = 0 := by
  have hmem : (1 + x + x ^ 2 : Module.End K V) w ∈ U := by
    have h1 := hxU w hw
    have h2 := hxU _ h1
    simp only [LinearMap.add_apply, Module.End.one_apply, sq, Module.End.mul_apply]
    exact U.add_mem (U.add_mem hw h1) h2
  apply hfp _ hmem
  have h3 : x * (1 + x + x ^ 2) = (1 + x + x ^ 2) + (x ^ 3 - 1) := by noncomm_ring
  rw [hx3, sub_self, add_zero] at h3
  rw [← Module.End.mul_apply, h3]

theorem finite_units_end [Finite K] [FiniteDimensional K V] : Finite (Module.End K V)ˣ := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (Module.End K V) :=
    Finite.of_injective (fun f : Module.End K V => (f : V → V)) DFunLike.coe_injective
  exact Finite.of_injective (fun u : (Module.End K V)ˣ => (u : Module.End K V)) Units.val_injective

theorem val_pow_apply (x : (Module.End K V)ˣ) (k : ℕ) (v : V) :
    ((x ^ k : (Module.End K V)ˣ) : Module.End K V) v = ((x : Module.End K V) ^ k) v := by
  rw [Units.val_pow_eq_pow_val]

theorem val_inv_apply_apply (x : (Module.End K V)ˣ) (v : V) :
    ((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((x : Module.End K V) v) = v := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

theorem triple_eq {R : Type*} [Ring R] {x y : R} (hc : x * y = y * x) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) : (y - 1) * (y - x) * (y - x ^ 2) = (1 + x + x ^ 2) * (x * y - y ^ 2) := by
  have h1 : y * x = x * y := hc.symm
  have h2 : y * x ^ 2 = x ^ 2 * y := by rw [sq, ← mul_assoc, h1, mul_assoc, h1, mul_assoc]
  have h3 : y ^ 2 * x ^ 2 = x ^ 2 * y ^ 2 := by
    rw [sq y, mul_assoc, h2, ← mul_assoc, h2, mul_assoc, ← sq]
  have h4 : y * x * y = x * y ^ 2 := by rw [h1, mul_assoc, ← sq]
  have e : (y - 1) * (y - x) * (y - x ^ 2) =
      y ^ 3 - y ^ 2 * x ^ 2 - y * x * y + y * x ^ 3 - y ^ 2 + y * x ^ 2 + x * y - x ^ 3 := by
    noncomm_ring
  have e2 : (1 + x + x ^ 2) * (x * y - y ^ 2) =
      x * y - y ^ 2 + x ^ 2 * y - x * y ^ 2 + x ^ 3 * y - x ^ 2 * y ^ 2 := by noncomm_ring
  rw [e, e2, h3, h4, h2, hx3, hy3]
  noncomm_ring

theorem exists_fixed_of_commute {x y : Module.End K V} (hc : x * y = y * x) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) {U : Submodule K V} (hxU : ∀ u ∈ U, x u ∈ U) (hyU : ∀ u ∈ U, y u ∈ U)
    (hfp : ∀ u ∈ U, x u = u → u = 0) (hU : U ≠ ⊥) :
    ∃ k : ℕ, k < 3 ∧ ∃ u ∈ U, u ≠ 0 ∧ y u = (x ^ k) u := by
  by_contra hcon
  push Not at hcon
  have hpow : ∀ k : ℕ, ∀ u ∈ U, (x ^ k) u ∈ U := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hxU u hu)
  have hsub : ∀ k : ℕ, k < 3 → ∀ u ∈ U, u ≠ 0 →
      (y - x ^ k) u ∈ U ∧ (y - x ^ k) u ≠ 0 := by
    intro k hk u hu hu0
    refine ⟨?_, ?_⟩
    · rw [LinearMap.sub_apply]
      exact U.sub_mem (hyU u hu) (hpow k u hu)
    · rw [LinearMap.sub_apply, sub_ne_zero]
      exact hcon k hk u hu hu0
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨hv1, hv10⟩ := hsub 2 (by norm_num) u hu hu0
  obtain ⟨hv2, hv20⟩ := hsub 1 (by norm_num) _ hv1 hv10
  obtain ⟨-, hv30⟩ := hsub 0 (by norm_num) _ hv2 hv20
  apply hv30
  rw [pow_one, pow_zero, ← Module.End.mul_apply, ← Module.End.mul_apply,
    triple_eq hc hx3 hy3, Module.End.mul_apply]
  apply sum_apply_eq_zero hx3 hxU hfp
  rw [LinearMap.sub_apply, Module.End.mul_apply, sq, Module.End.mul_apply]
  exact U.sub_mem (hxU _ (hyU u hu)) (hyU _ (hyU u hu))

theorem two_pow_odd_mod (k : ℕ) : 2 ^ (2 * k + 1) % 3 = 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

theorem even_of_two_pow_mod {u : ℕ} (h : 2 ^ u % 3 = 1) : Even u := by
  rcases Nat.even_or_odd u with he | ⟨k, rfl⟩
  · exact he
  · rw [two_pow_odd_mod k] at h
    exact absurd h (by norm_num)

theorem even_finrank_of_fpf [Finite K] (hK : Nat.card K = 2) [FiniteDimensional K V]
    {x : Module.End K V} (hx3 : x ^ 3 = 1) {U : Submodule K V} (hxU : ∀ u ∈ U, x u ∈ U)
    (hfp : ∀ u ∈ U, x u = u → u = 0) : Even (finrank K U) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Finite V := Module.finite_of_finite K
  have : Fintype U := Fintype.ofFinite U
  let f : Function.End U := fun u => ⟨x u, hxU u u.2⟩
  have hf3 : ∀ u : U, (f ^ 3) u = ⟨(x ^ 3) u, by rw [hx3]; exact u.2⟩ := by
    intro u
    rfl
  have hf : f ^ 3 ^ 1 = 1 := by
    funext u
    rw [pow_one, hf3]
    apply Subtype.ext
    change (x ^ 3) u = u
    rw [hx3, Module.End.one_apply]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  have hfix : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, by
      change f 0 = 0
      apply Subtype.ext
      change x 0 = 0
      rw [map_zero]⟩, ?_⟩
    rintro ⟨w, hw⟩
    apply Subtype.ext
    apply Subtype.ext
    have h1 : f w = w := hw
    have h2 : x w = w := congrArg Subtype.val h1
    exact hfp w w.2 h2
  have hcardU : Fintype.card U = 2 ^ finrank K U := by
    rw [Module.card_eq_pow_finrank (K := K), ← Nat.card_eq_fintype_card (α := K), hK]
  rw [hfix, hcardU] at hmod
  exact even_of_two_pow_mod hmod

end Basic

section Char2

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]

theorem two_eq_zero_end : (2 : Module.End K V) = 0 := by
  ext v
  rw [LinearMap.zero_apply, show (2 : Module.End K V) = 1 + 1 by norm_num, LinearMap.add_apply,
    Module.End.one_apply, ← two_smul K v, CharTwo.two_eq_zero, zero_smul]

theorem decomp_end (z : Module.End K V) : (z ^ 2 + z + 1) + z * (z - 1) = 1 := by
  have h : (z ^ 2 + z + 1) + z * (z - 1) = 2 * z ^ 2 + 1 := by noncomm_ring
  rw [h, two_eq_zero_end, zero_mul, zero_add]

theorem le_sup_ker_map {z : Module.End K V} (hz3 : z ^ 3 = 1) {U : Submodule K V}
    (hzU : ∀ u ∈ U, z u ∈ U) : U ≤ (U ⊓ LinearMap.ker (z - 1)) ⊔ U.map (z - 1) := by
  intro u hu
  have e : (z ^ 2 + z + 1 : Module.End K V) u + (z * (z - 1)) u = u := by
    rw [← LinearMap.add_apply, decomp_end, Module.End.one_apply]
  rw [← e]
  refine Submodule.add_mem_sup ⟨?_, ?_⟩ ?_
  · have h1 := hzU u hu
    have h2 := hzU _ h1
    simp only [LinearMap.add_apply, Module.End.one_apply, sq, Module.End.mul_apply]
    exact U.add_mem (U.add_mem h2 h1) hu
  · rw [SetLike.mem_coe, LinearMap.mem_ker, ← Module.End.mul_apply]
    have h3 : (z - 1) * (z ^ 2 + z + 1) = z ^ 3 - 1 := by noncomm_ring
    rw [h3, hz3, sub_self, LinearMap.zero_apply]
  · refine ⟨z u, hzU u hu, ?_⟩
    rw [← Module.End.mul_apply]
    congr 1
    noncomm_ring

theorem inf_ker_map_eq_bot {z : Module.End K V} (hz3 : z ^ 3 = 1) (U : Submodule K V) :
    (U ⊓ LinearMap.ker (z - 1)) ⊓ U.map (z - 1) = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨⟨-, hw⟩, ⟨v, -, rfl⟩⟩
  rw [Submodule.mem_bot]
  rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero] at hw
  have h1 : (z ^ 2 + z + 1 : Module.End K V) ((z - 1) v) = (z - 1) v := by
    simp only [LinearMap.add_apply, Module.End.one_apply, sq, Module.End.mul_apply]
    rw [hw, hw, add_assoc, ← two_smul K, CharTwo.two_eq_zero, zero_smul, add_zero]
  have h2 : (z ^ 2 + z + 1 : Module.End K V) ((z - 1) v) = 0 := by
    rw [← Module.End.mul_apply]
    have h3 : (z ^ 2 + z + 1) * (z - 1) = z ^ 3 - 1 := by noncomm_ring
    rw [h3, hz3, sub_self, LinearMap.zero_apply]
  rw [← h1, h2]

end Char2

section Index

variable {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

variable (hK : Nat.card K = 2)
include hK

theorem card_sq_le (n : ℕ) : ∀ (U : Submodule K V), finrank K U = n →
    ∀ X : Subgroup (Module.End K V)ˣ, (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) →
      (∀ x ∈ X, x ^ 3 = 1) → (∀ x ∈ X, ∀ u ∈ U, (x : Module.End K V) u ∈ U) →
      Nat.card X ^ 2 ≤ 3 ^ n * Nat.card (X ⊓ fixG U : Subgroup (Module.End K V)ˣ) ^ 2 := by
  have := finite_units_end (K := K) (V := V)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hUn X hcomm hexp hinv
  have hval3 : ∀ x ∈ X, (x : Module.End K V) ^ 3 = 1 := fun x hx => by
    rw [← Units.val_pow_eq_pow_val, hexp x hx, Units.val_one]
  have hcommE : ∀ x ∈ X, ∀ y ∈ X, (x : Module.End K V) * y = y * x := fun x hx y hy => by
    rw [← Units.val_mul, ← Units.val_mul, hcomm x hx y hy]
  by_cases hsplit : ∃ z ∈ X, (∃ u ∈ U, (z : Module.End K V) u ≠ u) ∧
      ∃ u ∈ U, u ≠ 0 ∧ (z : Module.End K V) u = u
  · obtain ⟨z, hzX, ⟨u₁, hu₁, hzu₁⟩, ⟨u₀, hu₀, hu₀0, hzu₀⟩⟩ := hsplit
    set z' : Module.End K V := (z : Module.End K V) with hz'
    have hz3 : z' ^ 3 = 1 := hval3 z hzX
    set U₁ := U ⊓ LinearMap.ker (z' - 1) with hU₁
    set U₂ := U.map (z' - 1) with hU₂
    have hinv₁ : ∀ x ∈ X, ∀ u ∈ U₁, (x : Module.End K V) u ∈ U₁ := by
      rintro x hx u ⟨hu, hku⟩
      refine ⟨hinv x hx u hu, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hku ⊢
      have hc' : (z' - 1) * (x : Module.End K V) = (x : Module.End K V) * (z' - 1) := by
        rw [sub_mul, mul_sub, one_mul, mul_one, hcommE x hx z hzX]
      rw [← Module.End.mul_apply, hc', Module.End.mul_apply, hku, map_zero]
    have hinv₂ : ∀ x ∈ X, ∀ u ∈ U₂, (x : Module.End K V) u ∈ U₂ := by
      rintro x hx _ ⟨u, hu, rfl⟩
      refine ⟨(x : Module.End K V) u, hinv x hx u hu, ?_⟩
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, mul_sub, sub_mul, mul_one, one_mul,
        hcommE x hx z hzX]
    have hle := le_sup_ker_map hz3 (hinv z hzX)
    have hbot := inf_ker_map_eq_bot hz3 U
    have hU₂U : U₂ ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact U.sub_mem (hinv z hzX u hu) hu
    have hsup : U₁ ⊔ U₂ = U := le_antisymm (sup_le inf_le_left hU₂U) hle
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
    rw [hsup, hbot, finrank_bot, add_zero, hUn] at hdim
    have hn₁ : 0 < finrank K U₁ := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨⟨u₀, hu₀, ?_⟩, fun h => hu₀0 (congrArg Subtype.val h)⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hzu₀,
        sub_self]
    have hn₂ : 0 < finrank K U₂ := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨⟨(z' - 1) u₁, u₁, hu₁, rfl⟩, fun h => hzu₁ ?_⟩
      have h1 : (z' - 1) u₁ = 0 := congrArg Subtype.val h
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    have h1 := ih (finrank K U₁) (by omega) U₁ rfl X hcomm hexp hinv₁
    set X' := X ⊓ fixG U₁ with hX'
    have h2 := ih (finrank K U₂) (by omega) U₂ rfl X'
      (fun x hx y hy => hcomm x hx.1 y hy.1) (fun x hx => hexp x hx.1)
      (fun x hx => hinv₂ x hx.1)
    have h3 : Nat.card (X' ⊓ fixG U₂ : Subgroup (Module.End K V)ˣ) ≤
        Nat.card (X ⊓ fixG U : Subgroup (Module.End K V)ˣ) := by
      refine Subgroup.card_le_of_le (le_inf (inf_le_left.trans inf_le_left) ?_)
      exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans (fixG_inf_le hle)
    calc Nat.card X ^ 2 ≤ 3 ^ finrank K U₁ * Nat.card X' ^ 2 := h1
      _ ≤ 3 ^ finrank K U₁ *
          (3 ^ finrank K U₂ * Nat.card (X' ⊓ fixG U₂ : Subgroup (Module.End K V)ˣ) ^ 2) :=
        Nat.mul_le_mul_left _ h2
      _ ≤ 3 ^ finrank K U₁ *
          (3 ^ finrank K U₂ * Nat.card (X ⊓ fixG U : Subgroup (Module.End K V)ˣ) ^ 2) := by
        gcongr
      _ = 3 ^ n * Nat.card (X ⊓ fixG U : Subgroup (Module.End K V)ˣ) ^ 2 := by
        rw [← mul_assoc, ← pow_add, hdim]
  · push Not at hsplit
    by_cases htriv : X ≤ fixG U
    · rw [inf_eq_left.mpr htriv]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    · obtain ⟨x, hxX, hxU⟩ := Set.not_subset.mp htriv
      have hx' : ∃ u ∈ U, (x : Module.End K V) u ≠ u := by
        by_contra hc
        push Not at hc
        exact hxU hc
      have hfp : ∀ u ∈ U, (x : Module.End K V) u = u → u = 0 := fun u hu h => by
        by_contra hu0
        exact hsplit x hxX hx' u hu hu0 h
      have hUbot : U ≠ ⊥ := by
        rintro rfl
        obtain ⟨u, hu, hxu⟩ := hx'
        rw [Submodule.mem_bot] at hu
        rw [hu, map_zero] at hxu
        exact hxu rfl
      have heven := even_finrank_of_fpf hK (hval3 x hxX) (hinv x hxX) hfp
      have hn0 : n ≠ 0 := by
        rw [← hUn]
        exact fun h => hUbot (Submodule.finrank_eq_zero.mp h)
      have hn2 : 2 ≤ n := by
        rw [hUn] at heven
        obtain ⟨m, hm⟩ := heven
        omega
      have hcov : ∀ y ∈ X, ∃ k : ℕ, k < 3 ∧ (x ^ k)⁻¹ * y ∈ X ⊓ fixG U := by
        intro y hy
        obtain ⟨k, hk, u, hu, hu0, hyu⟩ := exists_fixed_of_commute (hcommE x hxX y hy)
          (hval3 x hxX) (hval3 y hy) (hinv x hxX) (hinv y hy) hfp hUbot
        refine ⟨k, hk, X.mul_mem (X.inv_mem (X.pow_mem hxX k)) hy, ?_⟩
        have hzX : (x ^ k)⁻¹ * y ∈ X := X.mul_mem (X.inv_mem (X.pow_mem hxX k)) hy
        have hzu : (((x ^ k)⁻¹ * y : (Module.End K V)ˣ) : Module.End K V) u = u := by
          rw [Units.val_mul, Module.End.mul_apply, hyu, ← val_pow_apply, val_inv_apply_apply]
        intro w hw
        by_contra hzw
        exact hsplit _ hzX ⟨w, hw, hzw⟩ u hu hu0 hzu
      have hle3 : Nat.card X ≤ 3 * Nat.card (X ⊓ fixG U : Subgroup (Module.End K V)ˣ) := by
        let f : Fin 3 × (X ⊓ fixG U : Subgroup (Module.End K V)ˣ) → X :=
          fun kh => ⟨x ^ (kh.1 : ℕ) * kh.2, X.mul_mem (X.pow_mem hxX _) kh.2.2.1⟩
        have hf : Function.Surjective f := by
          rintro ⟨y, hy⟩
          obtain ⟨k, hk, hmem⟩ := hcov y hy
          refine ⟨(⟨k, hk⟩, ⟨_, hmem⟩), ?_⟩
          apply Subtype.ext
          change x ^ k * ((x ^ k)⁻¹ * y) = y
          group
        have := Nat.card_le_card_of_surjective f hf
        rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at this
      calc Nat.card X ^ 2 ≤ (3 * Nat.card (X ⊓ fixG U : Subgroup (Module.End K V)ˣ)) ^ 2 :=
            Nat.pow_le_pow_left hle3 2
        _ = 3 ^ 2 * Nat.card (X ⊓ fixG U : Subgroup (Module.End K V)ˣ) ^ 2 := by ring
        _ ≤ 3 ^ n * Nat.card (X ⊓ fixG U : Subgroup (Module.End K V)ˣ) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hn2)

theorem card_sq_le_top (X : Subgroup (Module.End K V)ˣ) (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hexp : ∀ x ∈ X, x ^ 3 = 1) : Nat.card X ^ 2 ≤ 3 ^ finrank K V := by
  have h := card_sq_le hK _ ⊤ rfl X hcomm hexp (fun _ _ _ _ => Submodule.mem_top)
  rwa [fixG_top, inf_bot_eq, Subgroup.card_bot, one_pow, mul_one, finrank_top] at h

theorem exists_end_node (X : Subgroup (Module.End K V)ˣ)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hexp : ∀ x ∈ X, x ^ 3 = 1) (hX : X ≠ ⊥)
    (hcard : 3 ^ finrank K V ≤ 3 * Nat.card X ^ 2) :
    ∃ g ∈ X, finrank K (LinearMap.range ((g : Module.End K V) - 1)) = 2 ∧
      ∀ x ∈ X, (∀ w, (g : Module.End K V) w = w → (x : Module.End K V) w = w) →
        x ∈ Subgroup.zpowers g := by
  classical
  have := finite_units_end (K := K) (V := V)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hval3 : ∀ x ∈ X, (x : Module.End K V) ^ 3 = 1 := fun x hx => by
    rw [← Units.val_pow_eq_pow_val, hexp x hx, Units.val_one]
  have hcommE : ∀ x ∈ X, ∀ y ∈ X, (x : Module.End K V) * y = y * x := fun x hx y hy => by
    rw [← Units.val_mul, ← Units.val_mul, hcomm x hx y hy]
  have hex : ∃ n, ∃ g ∈ X, g ≠ 1 ∧
      finrank K (LinearMap.range ((g : Module.End K V) - 1)) = n := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX
    exact ⟨_, g, hg, fun h => hg1 (Subtype.ext h), rfl⟩
  obtain ⟨g, hgX, hg1, hgm⟩ := Nat.find_spec hex
  have hmin : ∀ g' ∈ X, g' ≠ 1 →
      Nat.find hex ≤ finrank K (LinearMap.range ((g' : Module.End K V) - 1)) :=
    fun g' hg' hg'1 => Nat.find_min' hex ⟨g', hg', hg'1, rfl⟩
  set m := Nat.find hex with hm
  set g' : Module.End K V := (g : Module.End K V) with hg'
  set U := LinearMap.range (g' - 1) with hUdef
  set W := LinearMap.ker (g' - 1) with hWdef
  have hg3 : g' ^ 3 = 1 := hval3 g hgX
  have hmemW : ∀ w, w ∈ W ↔ g' w = w := fun w => by
    rw [hWdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hUW : U ⊓ W = ⊥ := by
    have h := inf_ker_map_eq_bot hg3 ⊤
    rwa [top_inf_eq, Submodule.map_top, inf_comm] at h
  have hrn : finrank K U + finrank K W = finrank K V := LinearMap.finrank_range_add_finrank_ker _
  have hUWtop : U ⊔ W = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hUW, finrank_bot, add_zero] at h
    omega
  have hcomm1 : ∀ x ∈ X, (x : Module.End K V) * (g' - 1) = (g' - 1) * x := fun x hx => by
    rw [mul_sub, sub_mul, mul_one, one_mul, hcommE x hx g hgX]
  have hinvU : ∀ x ∈ X, ∀ u ∈ U, (x : Module.End K V) u ∈ U := by
    rintro x hx _ ⟨v, rfl⟩
    exact ⟨(x : Module.End K V) v, by rw [← Module.End.mul_apply, ← Module.End.mul_apply,
      hcomm1 x hx]⟩
  have hinvW : ∀ x ∈ X, ∀ w ∈ W, (x : Module.End K V) w ∈ W := by
    intro x hx w hw
    rw [hWdef, LinearMap.mem_ker] at hw ⊢
    rw [← Module.End.mul_apply, ← hcomm1 x hx, Module.End.mul_apply, hw, map_zero]
  have hfp : ∀ u ∈ U, g' u = u → u = 0 := fun u hu h => by
    have : u ∈ U ⊓ W := ⟨hu, (hmemW u).mpr h⟩
    rwa [hUW, Submodule.mem_bot] at this
  have heven : Even m := hgm ▸ even_finrank_of_fpf hK hg3 (hinvU g hgX) hfp
  have hUbot : U ≠ ⊥ := by
    intro hU0
    apply hg1
    apply Units.ext
    apply LinearMap.ext
    intro v
    have hv : (g' - 1) v ∈ U := LinearMap.mem_range_self _ v
    rw [hU0, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    exact hv
  have hm0 : m ≠ 0 := by
    rw [← hgm]
    exact fun h => hUbot (Submodule.finrank_eq_zero.mp h)
  set Z := X ⊓ fixG W with hZdef
  have hW := card_sq_le hK _ W rfl X hcomm hexp hinvW
  have hU := card_sq_le hK _ U rfl Z (fun x hx y hy => hcomm x hx.1 y hy.1)
    (fun x hx => hexp x hx.1) (fun x hx => hinvU x hx.1)
  have hZU : Z ⊓ fixG U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ fixG (⊤ : Submodule K V) :=
      fixG_inf_le (by rw [sup_comm, hUWtop]) ⟨hx.1.2, hx.2⟩
    rwa [fixG_top] at h1
  rw [hZU, Subgroup.card_bot, one_pow, mul_one, hgm] at hU
  have hZ : 3 ^ m ≤ 3 * Nat.card Z ^ 2 := by
    have h1 : 3 ^ m * 3 ^ finrank K W ≤ 3 * Nat.card Z ^ 2 * 3 ^ finrank K W :=
      calc 3 ^ m * 3 ^ finrank K W = 3 ^ finrank K V := by rw [← pow_add, ← hrn, hgm]
        _ ≤ 3 * Nat.card X ^ 2 := hcard
        _ ≤ 3 * (3 ^ finrank K W * Nat.card Z ^ 2) := Nat.mul_le_mul_left 3 hW
        _ = 3 * Nat.card Z ^ 2 * 3 ^ finrank K W := by ring
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  have hgZ : Subgroup.zpowers g ≤ Z := by
    rw [Subgroup.zpowers_le]
    exact ⟨hgX, fun w hw => (hmemW w).mp hw⟩
  have hcardg : Nat.card (Subgroup.zpowers g) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hexp g hgX) hg1]
  have hm2 : m = 2 := by
    by_contra hm2
    have hm4 : 4 ≤ m := by
      obtain ⟨k, hk⟩ := heven
      omega
    have h27 : 27 ≤ Nat.card Z ^ 2 := by
      have := (Nat.pow_le_pow_right (by norm_num : 0 < 3) hm4).trans hZ
      omega
    have hnot : ¬ Z ≤ Subgroup.zpowers g := by
      intro hle
      have h1 := Subgroup.card_le_of_le hle
      rw [hcardg] at h1
      nlinarith
    obtain ⟨y, hyZ, hyg⟩ := Set.not_subset.mp hnot
    obtain ⟨k, -, u, hu, hu0, hyu⟩ := exists_fixed_of_commute (hcommE g hgX y hyZ.1) hg3
      (hval3 y hyZ.1) (hinvU g hgX) (hinvU y hyZ.1) hfp hUbot
    set z := (g ^ k)⁻¹ * y with hz
    have hzZ : z ∈ Z := Z.mul_mem (Z.inv_mem (Z.pow_mem (hgZ (Subgroup.mem_zpowers g)) k)) hyZ
    have hz1 : z ≠ 1 := by
      intro h
      apply hyg
      have hy : y = g ^ k := by
        rw [hz, inv_mul_eq_one] at h
        exact h.symm
      rw [hy]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) k
    have hzu : (z : Module.End K V) u = u := by
      rw [hz, Units.val_mul, Module.End.mul_apply, hyu, ← val_pow_apply, val_inv_apply_apply]
    have hker : W ⊔ Submodule.span K {u} ≤ LinearMap.ker ((z : Module.End K V) - 1) := by
      refine sup_le ?_ ?_
      · intro w hw
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hzZ.2 w hw, sub_self]
      · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
          LinearMap.sub_apply, Module.End.one_apply, hzu, sub_self]
    have hWu : W ⊓ Submodule.span K {u} = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hvW, hvu⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvu
      have h1 : c • u ∈ U ⊓ W := ⟨U.smul_mem c hu, hvW⟩
      rwa [hUW] at h1
    have hdimWu : finrank K (W ⊔ Submodule.span K {u} : Submodule K V) = finrank K W + 1 := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span K {u})
      rwa [hWu, finrank_bot, add_zero, finrank_span_singleton hu0] at h1
    have hrnz := LinearMap.finrank_range_add_finrank_ker ((z : Module.End K V) - 1)
    have hkle := Submodule.finrank_mono hker
    have h1 := hmin z hzZ.1 hz1
    omega
  refine ⟨g, hgX, hgm.trans hm2, fun x hx hxw => ?_⟩
  have hZg : Z = Subgroup.zpowers g := by
    refine (Subgroup.eq_of_le_of_card_ge hgZ ?_).symm
    rw [hcardg]
    rw [hm2] at hU
    nlinarith
  have hxZ : x ∈ Z := ⟨hx, fun w hw => hxw w ((hmemW w).mp hw)⟩
  rwa [hZg] at hxZ

end Index

end CFSG.StandardType.TwoThree
