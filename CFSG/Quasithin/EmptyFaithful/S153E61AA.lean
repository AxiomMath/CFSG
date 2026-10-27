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
public import Mathlib.GroupTheory.Nilpotent
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

namespace CFSG.Quasithin

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace S153E61A

theorem flag_base : ∀ x f : Fin 3 → ZMod 2, x ≠ 0 → f ≠ 0 → f ⬝ᵥ x = 0 →
    ∃ γ : Matrix (Fin 3) (Fin 3) (ZMod 2), γ *ᵥ ![1, 0, 0] = x ∧ γ.det = 1 ∧
      (γ.adjugate)ᵀ *ᵥ ![0, 1, 0] = f := by
  decide +kernel

theorem flag_base_inv {x f : Fin 3 → ZMod 2} (hx : x ≠ 0) (hf : f ≠ 0) (hfx : f ⬝ᵥ x = 0) :
    ∃ γ δ : Matrix (Fin 3) (Fin 3) (ZMod 2), γ * δ = 1 ∧ δ * γ = 1 ∧ γ *ᵥ ![1, 0, 0] = x ∧
      δᵀ *ᵥ ![0, 1, 0] = f := by
  obtain ⟨γ, h1, h2, h3⟩ := flag_base x f hx hf hfx
  refine ⟨γ, γ.adjugate, ?_, ?_, h1, h3⟩
  · rw [Matrix.mul_adjugate, h2, one_smul]
  · rw [Matrix.adjugate_mul, h2, one_smul]

theorem flag_trans {x f x' f' : Fin 3 → ZMod 2} (hx : x ≠ 0) (hf : f ≠ 0) (hfx : f ⬝ᵥ x = 0)
    (hx' : x' ≠ 0) (hf' : f' ≠ 0) (hfx' : f' ⬝ᵥ x' = 0) :
    ∃ γ δ : Matrix (Fin 3) (Fin 3) (ZMod 2), γ * δ = 1 ∧ δ * γ = 1 ∧ γ *ᵥ x = x' ∧ δᵀ *ᵥ f = f' := by
  obtain ⟨γ₁, δ₁, h11, h12, h13, h14⟩ := flag_base_inv hx hf hfx
  obtain ⟨γ₂, δ₂, h21, h22, h23, h24⟩ := flag_base_inv hx' hf' hfx'
  refine ⟨γ₂ * δ₁, γ₁ * δ₂, ?_, ?_, ?_, ?_⟩
  · calc γ₂ * δ₁ * (γ₁ * δ₂) = γ₂ * (δ₁ * γ₁) * δ₂ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h12, Matrix.mul_one, h21]
  · calc γ₁ * δ₂ * (γ₂ * δ₁) = γ₁ * (δ₂ * γ₂) * δ₁ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h22, Matrix.mul_one, h11]
  · rw [← h13, Matrix.mulVec_mulVec, Matrix.mul_assoc, h12, Matrix.mul_one, h23]
  · rw [← h14, Matrix.transpose_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.transpose_mul, h12,
      Matrix.transpose_one, Matrix.mul_one, h24]

theorem exists_flag_dual : ∀ x : Fin 3 → ZMod 2, x ≠ 0 → ∃ f : Fin 3 → ZMod 2, f ≠ 0 ∧ f ⬝ᵥ x = 0 := by
  decide

theorem exists_flag_nat : ∀ f : Fin 3 → ZMod 2, f ≠ 0 → ∃ x : Fin 3 → ZMod 2, x ≠ 0 ∧ f ⬝ᵥ x = 0 := by
  decide

theorem nat_trans {x x' : Fin 3 → ZMod 2} (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ∃ γ δ : Matrix (Fin 3) (Fin 3) (ZMod 2), γ * δ = 1 ∧ δ * γ = 1 ∧ γ *ᵥ x = x' := by
  obtain ⟨f, hf, hfx⟩ := exists_flag_dual x hx
  obtain ⟨f', hf', hfx'⟩ := exists_flag_dual x' hx'
  obtain ⟨γ, δ, h1, h2, h3, -⟩ := flag_trans hx hf hfx hx' hf' hfx'
  exact ⟨γ, δ, h1, h2, h3⟩

theorem dual_trans {f f' : Fin 3 → ZMod 2} (hf : f ≠ 0) (hf' : f' ≠ 0) :
    ∃ γ δ : Matrix (Fin 3) (Fin 3) (ZMod 2), γ * δ = 1 ∧ δ * γ = 1 ∧ δᵀ *ᵥ f = f' := by
  obtain ⟨x, hx, hfx⟩ := exists_flag_nat f hf
  obtain ⟨x', hx', hfx'⟩ := exists_flag_nat f' hf'
  obtain ⟨γ, δ, h1, h2, -, h4⟩ := flag_trans hx hf hfx hx' hf' hfx'
  exact ⟨γ, δ, h1, h2, h4⟩

end S153E61A

end CFSG.Quasithin
