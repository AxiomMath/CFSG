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

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open scoped MatrixGroups Matrix

@[expose] def FactNatPairEnd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (U V V₁ W K C : Subgroup G) (F : Type) [Field F]
    [Finite F] [CharP F 2] (α : ↥K →* SL(2, F)) (βV : ↥V →* Multiplicative (Fin 2 → F))
    (βU : ↥U →* Multiplicative (Fin 2 → F)),
    V₁ ≤ V → V ≤ U → V₁ ≤ W → W ≤ U → W ⊓ V = V₁ → W ⊔ V = U →
    (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ V₁) → (∀ a ∈ U, a ^ 2 ∈ V₁) →
    K ≤ Subgroup.normalizer (U : Set G) → K ≤ Subgroup.normalizer (V : Set G) →
    K ≤ Subgroup.normalizer (V₁ : Set G) → K ≤ Subgroup.normalizer (W : Set G) →
    Function.Surjective α → Function.Surjective βV → βV.ker = V₁.subgroupOf V →
    Function.Surjective βU → βU.ker = V.subgroupOf U →
    (∀ (k : ↥K) (a b : ↥V), (b : G) = k * a * k⁻¹ →
      Multiplicative.toAdd (βV b) =
        ((α k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (βV a)) →
    (∀ (k : ↥K) (a b : ↥U), (b : G) = k * a * k⁻¹ →
      Multiplicative.toAdd (βU b) =
        ((α k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (βU a)) →
    C ≤ Subgroup.normalizer (U : Set G) → C ≤ Subgroup.normalizer (V₁ : Set G) →
    (∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ U) →
    ∃ Ψ : ↥C →* GL (Fin 2) F,
      (∀ c : ↥C, Ψ c = 1 ↔ ∀ u ∈ U, (c : G) * u * (c : G)⁻¹ * u⁻¹ ∈ V₁) ∧
      ∀ (c : ↥C) (r s : F), (c : G) ∈ Subgroup.normalizer (V : Set G) →
        (∀ a b : ↥V, (b : G) = c * a * (c : G)⁻¹ →
          Multiplicative.toAdd (βV b) = r • Multiplicative.toAdd (βV a)) →
        (∀ a b : ↥U, (b : G) = c * a * (c : G)⁻¹ →
          Multiplicative.toAdd (βU b) = s • Multiplicative.toAdd (βU a)) →
        (Ψ c : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧ (Ψ c : Matrix (Fin 2) (Fin 2) F) 0 0 = r ∧
          (Ψ c : Matrix (Fin 2) (Fin 2) F) 1 1 = s

@[expose] def FactDicksonGL2 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (Y : Subgroup (GL (Fin 2) F))
    (g : GL (Fin 2) F),
    (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ (g : Matrix (Fin 2) (Fin 2) F) 1 1 →
    (∀ y ∈ Y, g * y * g⁻¹ ∈ Y) → Nat.Coprime (Nat.card Y) (Nat.card F - 1) → IsPGroup 2 Y

end CFSG.Quasithin.Vol2.Ch11.SecJ
