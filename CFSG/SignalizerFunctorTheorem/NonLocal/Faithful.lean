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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem faithful_of_simple {X Γ : Type*} [Group X] [Group Γ] (ψ : Γ →* X)
    (hsimple : IsSimpleGroup ψ.range) (V : Subgroup X) (hV0 : V ≠ ⊥)
    (hnorm : ∀ c ∈ ψ.range, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (hcent : ∀ x : X, (∀ g : Γ, x * ψ g = ψ g * x) → x = 1) :
    ∀ g : Γ, (∀ v ∈ V, ψ g * v * (ψ g)⁻¹ = v) → ψ g = 1 := by
  let C₀ : Subgroup X := ψ.range
  let Kv : Subgroup C₀ :=
    { carrier := {c | ∀ v ∈ V, (c : X) * v = v * (c : X)}
      mul_mem' := fun {a b} ha hb v hv => by
        calc ((a * b : C₀) : X) * v = (a : X) * ((b : X) * v) := by simp [mul_assoc]
          _ = (a : X) * (v * (b : X)) := by rw [hb v hv]
          _ = ((a : X) * v) * (b : X) := by simp [mul_assoc]
          _ = (v * (a : X)) * (b : X) := by rw [ha v hv]
          _ = v * ((a * b : C₀) : X) := by simp [mul_assoc]
      one_mem' := fun v _ => by simp
      inv_mem' := fun {a} ha v hv => by
        have h2 := ha v hv
        calc ((a⁻¹ : C₀) : X) * v = ((a : X)⁻¹ * v * (a : X)) * (a : X)⁻¹ := by
              simp [mul_assoc]
          _ = ((a : X)⁻¹ * (v * (a : X))) * (a : X)⁻¹ := by simp [mul_assoc]
          _ = ((a : X)⁻¹ * ((a : X) * v)) * (a : X)⁻¹ := by rw [h2]
          _ = v * ((a⁻¹ : C₀) : X) := by simp }
  have hKvN : Kv.Normal := ⟨fun c hc d v hv => by
    show ((d * c * d⁻¹ : C₀) : X) * v = v * ((d * c * d⁻¹ : C₀) : X)
    have hd1 : (d : X)⁻¹ * v * ((d : X)⁻¹)⁻¹ ∈ V := by
      have := hnorm ((d⁻¹ : C₀) : X) (d⁻¹).2 v hv
      simpa using this
    have h3 := hc _ hd1
    calc ((d * c * d⁻¹ : C₀) : X) * v
        = (d : X) * ((c : X) * ((d : X)⁻¹ * v * (d : X))) * (d : X)⁻¹ := by
          simp [mul_assoc]
      _ = (d : X) * (((d : X)⁻¹ * v * (d : X)) * (c : X)) * (d : X)⁻¹ := by
          have := hc ((d : X)⁻¹ * v * (d : X)) (by simpa using hd1)
          rw [this]
      _ = v * ((d * c * d⁻¹ : C₀) : X) := by simp [mul_assoc]⟩
  intro g hg
  have hg' : (⟨ψ g, g, rfl⟩ : C₀) ∈ Kv := by
    intro v hv
    have := hg v hv
    calc ψ g * v = (ψ g * v * (ψ g)⁻¹) * ψ g := by simp [mul_assoc]
      _ = v * ψ g := by rw [this]
  have := hKvN
  rcases hsimple.eq_bot_or_eq_top_of_normal Kv with hbot | htop
  · rw [hbot, Subgroup.mem_bot] at hg'
    exact congrArg Subtype.val hg'
  · exfalso
    apply hV0
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    apply hcent v
    intro g'
    have h1 := (show (⟨ψ g', g', rfl⟩ : C₀) ∈ Kv by rw [htop]; exact Subgroup.mem_top _) v hv
    exact h1.symm

end CFSG.SignalizerFunctorTheorem.NonLocal
