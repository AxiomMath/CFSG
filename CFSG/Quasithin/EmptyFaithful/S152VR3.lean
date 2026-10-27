module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.S152V

open Equiv Equiv.Perm

theorem no_commuting_involution_of_sylow {Ĝ : Type*} [Group Ĝ] [Finite Ĝ] (A : Subgroup Ĝ) (m : ℕ)
    (hA : Nat.card A = 9 * m) (hm : ¬ 3 ∣ m) (H₀ : Subgroup Ĝ) (hH₀A : H₀ ≤ A)
    (hH₀ : Nat.card H₀ = 9) (hC : ∀ s : Ĝ, (∀ h ∈ H₀, s * h = h * s) → s ^ 9 = 1)
    (H : Subgroup Ĝ) (hHA : H ≤ A) (hH : Nat.card H = 9) (σ : Ĝ) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hcomm : ∀ h ∈ H, σ * h = h * σ) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H₁ : Subgroup ↥A := H.subgroupOf A
  let K₁ : Subgroup ↥A := H₀.subgroupOf A
  have hH₁ : Nat.card H₁ = 9 := (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv).trans hH
  have hK₁ : Nat.card K₁ = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₀A).toEquiv).trans hH₀
  have hp₁ : IsPGroup 3 H₁ := IsPGroup.of_card (n := 2) (by rw [hH₁]; norm_num)
  have hq₁ : IsPGroup 3 K₁ := IsPGroup.of_card (n := 2) (by rw [hK₁]; norm_num)
  have hidx₁ : ¬ 3 ∣ H₁.index := by
    have h := Subgroup.card_mul_index H₁
    rw [hH₁, hA] at h
    have h2 : H₁.index = m := by omega
    rwa [h2]
  have hidx₂ : ¬ 3 ∣ K₁.index := by
    have h := Subgroup.card_mul_index K₁
    rw [hK₁, hA] at h
    have h2 : K₁.index = m := by omega
    rwa [h2]
  let S₁ : Sylow 3 ↥A := hp₁.toSylow hidx₁
  let S₀ : Sylow 3 ↥A := hq₁.toSylow hidx₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥A S₀ S₁
  have hS₁ : (S₁ : Subgroup ↥A) = H₁ := IsPGroup.toSylow_coe _ _
  have hS₀ : (S₀ : Subgroup ↥A) = K₁ := IsPGroup.toSylow_coe _ _
  have hconj : ∀ h₀ ∈ H₀, ((g : Ĝ) * h₀ * (g : Ĝ)⁻¹) ∈ H := by
    intro h₀ hh₀
    have hmem : (⟨h₀, hH₀A hh₀⟩ : ↥A) ∈ (S₀ : Subgroup ↥A) := by
      rw [hS₀]
      exact hh₀
    have h1 : g * (⟨h₀, hH₀A hh₀⟩ : ↥A) * g⁻¹ ∈ ((g • S₀ : Sylow 3 ↥A) : Subgroup ↥A) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨_, hmem, rfl⟩
    rw [hg, hS₁] at h1
    exact h1
  have hσ' : ∀ h₀ ∈ H₀, ((g : Ĝ)⁻¹ * σ * (g : Ĝ)) * h₀ = h₀ * ((g : Ĝ)⁻¹ * σ * (g : Ĝ)) := by
    intro h₀ hh₀
    have h1 := hcomm _ (hconj h₀ hh₀)
    calc ((g : Ĝ)⁻¹ * σ * (g : Ĝ)) * h₀
        = (g : Ĝ)⁻¹ * (σ * ((g : Ĝ) * h₀ * (g : Ĝ)⁻¹)) * (g : Ĝ) := by group
      _ = (g : Ĝ)⁻¹ * (((g : Ĝ) * h₀ * (g : Ĝ)⁻¹) * σ) * (g : Ĝ) := by rw [h1]
      _ = h₀ * ((g : Ĝ)⁻¹ * σ * (g : Ĝ)) := by group
  have h9 := hC _ hσ'
  set τ : Ĝ := (g : Ĝ)⁻¹ * σ * (g : Ĝ) with hτ
  have h2 : τ ^ 2 = 1 := by
    have : τ ^ 2 = (g : Ĝ)⁻¹ * (σ * σ) * (g : Ĝ) := by
      rw [pow_two, hτ]
      group
    rw [this, ← pow_two, hσ2]
    group
  have h1 : τ = 1 := by
    rw [show 9 = 1 + 8 from rfl, pow_add, pow_one] at h9
    have h8 : τ ^ 8 = 1 := by
      rw [show 8 = 2 * 4 from rfl, pow_mul, h2, one_pow]
    rw [h8, mul_one] at h9
    exact h9
  apply hσ1
  have : σ = (g : Ĝ) * τ * (g : Ĝ)⁻¹ := by
    rw [hτ]
    group
  rw [this, h1]
  group

section E9

variable {Ĝ : Type*} [Group Ĝ]

theorem pow_val_add (c : Ĝ) (hc : c ^ 3 = 1) (x y : ZMod 3) :
    c ^ (x + y).val = c ^ x.val * c ^ y.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod (x.val + y.val) hc, pow_add]

@[expose] def e9Hom (a b : Ĝ) (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    Multiplicative (ZMod 3 × ZMod 3) →* Ĝ where
  toFun x := a ^ (Multiplicative.toAdd x).1.val * b ^ (Multiplicative.toAdd x).2.val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    rw [pow_val_add a ha, pow_val_add b hb]
    calc a ^ (Multiplicative.toAdd x).1.val * a ^ (Multiplicative.toAdd y).1.val *
          (b ^ (Multiplicative.toAdd x).2.val * b ^ (Multiplicative.toAdd y).2.val)
        = a ^ (Multiplicative.toAdd x).1.val *
          (a ^ (Multiplicative.toAdd y).1.val * b ^ (Multiplicative.toAdd x).2.val) *
          b ^ (Multiplicative.toAdd y).2.val := by group
      _ = a ^ (Multiplicative.toAdd x).1.val *
          (b ^ (Multiplicative.toAdd x).2.val * a ^ (Multiplicative.toAdd y).1.val) *
          b ^ (Multiplicative.toAdd y).2.val := by
        rw [(hab.pow_pow (Multiplicative.toAdd y).1.val (Multiplicative.toAdd x).2.val).eq]
      _ = _ := by group

theorem e9Hom_apply (a b : Ĝ) (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (i j : ZMod 3) :
    e9Hom a b hab ha hb (Multiplicative.ofAdd (i, j)) = a ^ i.val * b ^ j.val := rfl

theorem e9Hom_exp (a b : Ĝ) (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    ∀ g ∈ (e9Hom a b hab ha hb).range, g ^ 3 = 1 := by
  rintro _ ⟨x, rfl⟩
  rw [← map_pow]
  have : x ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_one]
    have h3 : ((3 : ℕ) : ZMod 3 × ZMod 3) = 0 := by decide
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3 × ZMod 3), h3, zero_smul]
  rw [this, map_one]

theorem e9Hom_comm (a b : Ĝ) (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    ∀ g ∈ (e9Hom a b hab ha hb).range, ∀ h ∈ (e9Hom a b hab ha hb).range, g * h = h * g := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem e9Hom_card (a b : Ĝ) (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hinj : ∀ p q : ZMod 3 × ZMod 3,
      a ^ p.1.val * b ^ p.2.val = a ^ q.1.val * b ^ q.2.val → p = q) :
    Nat.card (e9Hom a b hab ha hb).range = 9 := by
  have hi : Function.Injective (e9Hom a b hab ha hb) := by
    intro x y hxy
    have := hinj (Multiplicative.toAdd x) (Multiplicative.toAdd y) hxy
    exact Multiplicative.toAdd.injective this
  rw [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
  simp

theorem e9Hom_mem_left (a b : Ĝ) (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    a ∈ (e9Hom a b hab ha hb).range :=
  ⟨Multiplicative.ofAdd (1, 0), by
    rw [e9Hom_apply]
    have h1 : (1 : ZMod 3).val = 1 := by decide
    simp [h1]⟩

theorem e9Hom_mem_right (a b : Ĝ) (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    b ∈ (e9Hom a b hab ha hb).range :=
  ⟨Multiplicative.ofAdd (0, 1), by
    rw [e9Hom_apply]
    have h1 : (1 : ZMod 3).val = 1 := by decide
    simp [h1]⟩

end E9

@[expose] def c6a : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def c6b : Perm (Fin 6) := swap 3 4 * swap 4 5

theorem c6a_cube : c6a ^ 3 = 1 := by unfold c6a; decide +kernel

theorem c6b_cube : c6b ^ 3 = 1 := by unfold c6b; decide +kernel

theorem c6_comm : Commute c6a c6b := by
  show c6a * c6b = c6b * c6a
  unfold c6a c6b
  decide +kernel

theorem c6a_sign : Perm.sign c6a = 1 := by unfold c6a; decide +kernel

theorem c6b_sign : Perm.sign c6b = 1 := by unfold c6b; decide +kernel

theorem c6_inj : ∀ p q : ZMod 3 × ZMod 3,
    c6a ^ p.1.val * c6b ^ p.2.val = c6a ^ q.1.val * c6b ^ q.2.val → p = q := by
  unfold c6a c6b
  decide +kernel

theorem c6_cent : ∀ s : Perm (Fin 6), s * c6a = c6a * s → s * c6b = c6b * s → s ^ 9 = 1 := by
  unfold c6a c6b
  decide +kernel

@[expose] def H6 : Subgroup (Perm (Fin 6)) := (e9Hom c6a c6b c6_comm c6a_cube c6b_cube).range

theorem H6_card : Nat.card H6 = 9 := e9Hom_card _ _ _ _ _ c6_inj

theorem H6_sign : ∀ g ∈ H6, Perm.sign g = 1 := by
  rintro _ ⟨x, rfl⟩
  simp [e9Hom, map_mul, map_pow, c6a_sign, c6b_sign]

theorem H6_alt : H6 ≤ alternatingGroup (Fin 6) := fun g hg => mem_alternatingGroup.2 (H6_sign g hg)

theorem H6_comm : ∀ g ∈ H6, ∀ h ∈ H6, g * h = h * g := e9Hom_comm _ _ _ _ _

theorem H6_exp : ∀ g ∈ H6, g ^ 3 = 1 := e9Hom_exp _ _ _ _ _

theorem no_commuting_involution_alt6 (H : Subgroup (Perm (Fin 6))) (hHA : H ≤ alternatingGroup (Fin 6))
    (hH : Nat.card H = 9) (σ : Perm (Fin 6)) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hcomm : ∀ h ∈ H, σ * h = h * σ) : False := by
  refine no_commuting_involution_of_sylow (alternatingGroup (Fin 6)) 40 ?_ (by norm_num) H6
    H6_alt H6_card ?_ H hHA hH σ hσ2 hσ1 hcomm
  · rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  · intro s h
    exact c6_cent s (h c6a (e9Hom_mem_left _ _ _ _ _)) (h c6b (e9Hom_mem_right _ _ _ _ _))

@[expose] def c7a : Perm (Fin 7) := swap 0 1 * swap 1 2

@[expose] def c7b : Perm (Fin 7) := swap 3 4 * swap 4 5

theorem c7a_cube : c7a ^ 3 = 1 := by unfold c7a; decide +kernel

theorem c7b_cube : c7b ^ 3 = 1 := by unfold c7b; decide +kernel

theorem c7_comm : Commute c7a c7b := by
  show c7a * c7b = c7b * c7a
  unfold c7a c7b
  decide +kernel

theorem c7a_sign : Perm.sign c7a = 1 := by unfold c7a; decide +kernel

theorem c7b_sign : Perm.sign c7b = 1 := by unfold c7b; decide +kernel

set_option maxRecDepth 1000000 in
theorem c7_inj : ∀ p q : ZMod 3 × ZMod 3,
    c7a ^ p.1.val * c7b ^ p.2.val = c7a ^ q.1.val * c7b ^ q.2.val → p = q := by
  unfold c7a c7b
  decide +kernel

set_option maxRecDepth 1000000 in
theorem c7_cent : ∀ s : Perm (Fin 7), s * c7a = c7a * s → s * c7b = c7b * s → s ^ 9 = 1 := by
  unfold c7a c7b
  decide +kernel

@[expose] def H7 : Subgroup (Perm (Fin 7)) := (e9Hom c7a c7b c7_comm c7a_cube c7b_cube).range

theorem H7_card : Nat.card H7 = 9 := e9Hom_card _ _ _ _ _ c7_inj

theorem H7_sign : ∀ g ∈ H7, Perm.sign g = 1 := by
  rintro _ ⟨x, rfl⟩
  simp [e9Hom, map_mul, map_pow, c7a_sign, c7b_sign]

theorem H7_alt : H7 ≤ alternatingGroup (Fin 7) := fun g hg => mem_alternatingGroup.2 (H7_sign g hg)

theorem H7_comm : ∀ g ∈ H7, ∀ h ∈ H7, g * h = h * g := e9Hom_comm _ _ _ _ _

theorem H7_exp : ∀ g ∈ H7, g ^ 3 = 1 := e9Hom_exp _ _ _ _ _

theorem no_commuting_involution_alt7 (H : Subgroup (Perm (Fin 7))) (hHA : H ≤ alternatingGroup (Fin 7))
    (hH : Nat.card H = 9) (σ : Perm (Fin 7)) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hcomm : ∀ h ∈ H, σ * h = h * σ) : False := by
  refine no_commuting_involution_of_sylow (alternatingGroup (Fin 7)) 280 ?_ (by norm_num) H7
    H7_alt H7_card ?_ H hHA hH σ hσ2 hσ1 hcomm
  · rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  · intro s h
    exact c7_cent s (h c7a (e9Hom_mem_left _ _ _ _ _)) (h c7b (e9Hom_mem_right _ _ _ _ _))

end CFSG.Quasithin.S152V
