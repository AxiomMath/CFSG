module

public import CFSG.GroupTheory.LocalCores.Components
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

namespace CFSG.RankThree.PartOne.KE

open scoped Pointwise commutatorElement

theorem commutator_mem_of_mem_sup_normalizer {G : Type*} [Group G] {H Q : Subgroup G}
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {y₁ y₂ : G} (h₁ : y₁ ∈ H ⊔ Q) (h₂ : y₂ ∈ H ⊔ Q) : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ Q := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right H Q hHQ
  have h₁' : y₁ ∈ (H : Set G) * (Q : Set G) := by rw [← hmul]; exact h₁
  have h₂' : y₂ ∈ (H : Set G) * (Q : Set G) := by rw [← hmul]; exact h₂
  obtain ⟨t₁, ht₁, q₁, hq₁, rfl⟩ := h₁'
  obtain ⟨t₂, ht₂, q₂, hq₂, rfl⟩ := h₂'
  have hQ : ∀ t ∈ H, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := fun t ht q hq =>
    (Subgroup.mem_normalizer_iff.1 (hHQ ht) q).1 hq
  have hQ' : ∀ t ∈ H, ∀ q ∈ Q, t⁻¹ * q * t ∈ Q := fun t ht q hq => by
    have := (Subgroup.mem_normalizer_iff.1 (hHQ (inv_mem ht)) q).1 hq
    simpa using this
  have hc' : t₂ * t₁ * t₂⁻¹ = t₁ := by
    rw [← hHc t₁ ht₁ t₂ ht₂, mul_assoc, mul_inv_cancel, mul_one]
  have hq5 : t₁ * ((t₂⁻¹ * q₁ * t₂) * q₁⁻¹) * t₁⁻¹ ∈ Q :=
    hQ t₁ ht₁ _ (mul_mem (hQ' t₂ ht₂ q₁ hq₁) (inv_mem hq₁))
  have hq6 : t₁ * (q₁ * q₂ * q₁⁻¹) * t₁⁻¹ ∈ Q :=
    hQ t₁ ht₁ _ (mul_mem (mul_mem hq₁ hq₂) (inv_mem hq₁))
  have hq4 : t₂ * (t₁ * ((t₂⁻¹ * q₁ * t₂) * q₁⁻¹) * t₁⁻¹ *
      (t₁ * (q₁ * q₂ * q₁⁻¹) * t₁⁻¹) * q₂⁻¹) * t₂⁻¹ ∈ Q :=
    hQ t₂ ht₂ _ (mul_mem (mul_mem hq5 hq6) (inv_mem hq₂))
  have e : t₁ * q₁ * (t₂ * q₂) * (t₁ * q₁)⁻¹ * (t₂ * q₂)⁻¹ =
      t₂ * (t₁ * ((t₂⁻¹ * q₁ * t₂) * q₁⁻¹) * t₁⁻¹ * (t₁ * (q₁ * q₂ * q₁⁻¹) * t₁⁻¹) * q₂⁻¹) *
        t₂⁻¹ := by
    calc t₁ * q₁ * (t₂ * q₂) * (t₁ * q₁)⁻¹ * (t₂ * q₂)⁻¹
        = (t₂ * t₁ * t₂⁻¹) * q₁ * t₂ * q₂ * q₁⁻¹ * t₁⁻¹ * q₂⁻¹ * t₂⁻¹ := by
          rw [hc']
          group
      _ = _ := by group
  rw [e]
  exact hq4

theorem commutator_range_eq_of_family {D G : Type*} [Group D] [Group G] (ψ : D →* G)
    {H Q R P : Subgroup G} (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hψ : ∀ y, ψ y ∈ H ⊔ Q) (hψR : ∀ y, ψ y ∈ R)
    (hP : P = Q ⊓ R) (hPψ : P ≤ ψ.range) (hPperf : ⁅P, P⁆ = P) :
    ⁅ψ.range, ψ.range⁆ = P := by
  refine le_antisymm (Subgroup.commutator_le.2 ?_) ?_
  · rintro _ ⟨y₁, rfl⟩ _ ⟨y₂, rfl⟩
    rw [hP, commutatorElement_def]
    exact Subgroup.mem_inf.2 ⟨commutator_mem_of_mem_sup_normalizer hHQ hHc (hψ y₁) (hψ y₂),
      mul_mem (mul_mem (mul_mem (hψR y₁) (hψR y₂)) (inv_mem (hψR y₁))) (inv_mem (hψR y₂))⟩
  · calc P = ⁅P, P⁆ := hPperf.symm
      _ ≤ ⁅ψ.range, ψ.range⁆ := Subgroup.commutator_mono hPψ hPψ

theorem isQuasisimple_commutator_of_embedding {C G : Type*} [Group C] [Group G] {D : Subgroup C}
    (ψ : D →* G) (hψ : Function.Injective ψ) {P : Subgroup G} (hP : CFSG.IsQuasisimple P)
    (h : ⁅ψ.range, ψ.range⁆ = P) :
    CFSG.IsQuasisimple (⁅D, D⁆ : Subgroup C) ∧
      (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆).map ψ = P ∧
      (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆).map D.subtype = ⁅D, D⁆ := by
  have h1 : (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆).map D.subtype = ⁅D, D⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h2 : (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆).map ψ = P := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, h]
  refine ⟨?_, h2, h1⟩
  set T' : Subgroup D := ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ with hT'
  have e1 : T' ≃* (T'.map ψ) := Subgroup.equivMapOfInjective _ ψ hψ
  have e2 : T' ≃* (⁅D, D⁆ : Subgroup C) :=
    (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective).trans
      (MulEquiv.subgroupCongr h1)
  have e3 : T' ≃* P := e1.trans (MulEquiv.subgroupCongr h2)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e3.symm.trans e2) hP

end CFSG.RankThree.PartOne.KE
