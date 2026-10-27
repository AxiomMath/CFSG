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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.L34Amalgam

structure IsParabolic {L : Type*} [Group L] (K E : Subgroup L) (a b : L) : Prop where
  le : E ≤ K
  normal : ∀ x ∈ K, ∀ e ∈ E, x * e * x⁻¹ ∈ E
  mul_self : ∀ e ∈ E, e * e = 1
  card_E : Nat.card E = 16
  card : Nat.card K = 960
  mem_a : a ∈ K
  mem_b : b ∈ K
  inf : E ⊓ Subgroup.closure {a, b} = ⊥
  card_C : Nat.card (Subgroup.closure {a, b}) = 60
  ha : a * a = 1
  hb : b ^ 3 = 1
  hab : (a * b) ^ 5 = 1
  fpf : ∀ e ∈ E, b * e = e * b → e = 1

namespace IsParabolic

variable {L : Type*} [Group L] {K E : Subgroup L} {a b : L}

theorem closure_le (h : IsParabolic K E a b) : Subgroup.closure {a, b} ≤ K := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact h.mem_a
  · exact h.mem_b

theorem normal_subgroupOf (h : IsParabolic K E a b) : (E.subgroupOf K).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact h.normal _ g.2 _ hn⟩

theorem closure_subgroupOf (h : IsParabolic K E a b) :
    Subgroup.closure {(⟨a, h.mem_a⟩ : ↥K), ⟨b, h.mem_b⟩} =
      (Subgroup.closure {a, b}).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le h.closure_le]
  congr 1
  ext g
  simp

theorem map {L' : Type*} [Group L'] (h : IsParabolic K E a b) (f : L →* L')
    (hf : Function.Injective f) : IsParabolic (K.map f) (E.map f) (f a) (f b) := by
  have hcl : Subgroup.closure {f a, f b} = (Subgroup.closure {a, b}).map f := by
    rw [MonoidHom.map_closure, Set.image_pair]
  refine ⟨Subgroup.map_mono h.le, ?_, ?_, ?_, ?_, ⟨a, h.mem_a, rfl⟩, ⟨b, h.mem_b, rfl⟩, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨e, he, rfl⟩
    exact ⟨x * e * x⁻¹, h.normal x hx e he, by rw [map_mul, map_mul, map_inv]⟩
  · rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, h.mul_self e he, map_one]
  · rw [Subgroup.card_map_of_injective hf, h.card_E]
  · rw [Subgroup.card_map_of_injective hf, h.card]
  · rw [hcl, ← Subgroup.map_inf_eq _ _ f hf, h.inf, Subgroup.map_bot]
  · rw [hcl, Subgroup.card_map_of_injective hf, h.card_C]
  · rw [← map_mul, h.ha, map_one]
  · rw [← map_pow, h.hb, map_one]
  · rw [← map_mul, ← map_pow, h.hab, map_one]
  · rintro _ ⟨e, he, rfl⟩ hc
    rw [← map_mul, ← map_mul] at hc
    rw [h.fpf e he (hf hc), map_one]

end IsParabolic

end CFSG.Quasithin.L34Amalgam
