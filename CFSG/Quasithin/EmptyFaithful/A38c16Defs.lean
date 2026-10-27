module

public import CFSG.Quasithin.EmptyFaithful.A38c16Data
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

namespace CFSG.Quasithin.A38c16

open scoped MatrixGroups

section Sub

variable {W : Type} [CommGroup W]

@[expose] def IsKSub (K : Subgroup (MulAut W)) (M : Subgroup W) : Prop :=
  ∀ k ∈ K, ∀ v ∈ M, k v ∈ M

@[expose] def IsSimple8 (K : Subgroup (MulAut W)) (M : Subgroup W) : Prop :=
  IsKSub K M ∧ Nat.card M = 8 ∧ ∀ N : Subgroup W, N ≤ M → IsKSub K N → N = ⊥ ∨ N = M

@[expose] def IsOuterOn (K : Subgroup (MulAut W)) (s : MulAut W) : Prop :=
  ¬ ∃ g ∈ K, ∀ x ∈ K, s * x * s⁻¹ = g * x * g⁻¹

structure Case3Setting (Γ K Kp : Subgroup (MulAut W)) : Prop where
  K_le : K ≤ Γ
  Kp_le : Kp ≤ Γ
  K_norm : ∀ g ∈ Γ, ∀ k ∈ K, g * k * g⁻¹ ∈ K
  Kp_norm : ∀ g ∈ Γ, ∀ k ∈ Kp, g * k * g⁻¹ ∈ Kp
  comm : ∀ k ∈ K, ∀ y ∈ Kp, k * y = y * k
  cent : ∀ γ ∈ Γ, (∀ k ∈ K, γ * k = k * γ) → (∀ y ∈ Kp, γ * y = y * γ) → γ = 1

end Sub

section Out

open Classical in
@[expose] noncomputable def outerClass (α : SL(3, ZMod 2) ≃* SL(3, ZMod 2)) : ZMod 2 :=
  if ∃ g : SL(3, ZMod 2), ∀ x, α x = g * x * g⁻¹ then 0 else 1

structure SL3OutFacts : Prop where
  trans : ∀ α β : SL(3, ZMod 2) ≃* SL(3, ZMod 2),
    outerClass (α.trans β) = outerClass α + outerClass β
  inner : ∀ α : SL(3, ZMod 2) ≃* SL(3, ZMod 2), outerClass α = 0 →
    ∃ g : SL(3, ZMod 2), ∀ x, α x = g * x * g⁻¹
  card_fix : ∀ (α₁ α₂ : SL(3, ZMod 2) ≃* SL(3, ZMod 2)) (t : ZMod 2 × ZMod 2)
    (E : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2))),
    Nat.card (fixSetT t (E.map (MulEquiv.prodCongr α₁ α₂).toMonoidHom)) =
      Nat.card (fixSetT (t + (outerClass α₁, outerClass α₂)) E)
  distinguish : ∀ t t' : ZMod 2 × ZMod 2, t ≠ t' →
    ∃ E : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2)), Nat.card (fixSetT t E) ≠ Nat.card (fixSetT t' E)

end Out

end CFSG.Quasithin.A38c16
