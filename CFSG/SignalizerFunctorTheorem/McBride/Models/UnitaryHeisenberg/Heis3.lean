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
public import Mathlib.Tactic.Basify
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

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg

@[ext] structure Heis3 where
  x : ZMod 3
  y : ZMod 3
  z : ZMod 3

namespace Heis3

instance : DecidableEq Heis3 := fun p q =>
  decidable_of_iff (p.x = q.x ∧ p.y = q.y ∧ p.z = q.z)
    ⟨fun ⟨h1, h2, h3⟩ => by ext <;> assumption, fun h => by simp [h]⟩

instance : Mul Heis3 := ⟨fun p q => ⟨p.x + q.x, p.y + q.y, p.z + q.z + p.y * q.x⟩⟩

instance : One Heis3 := ⟨⟨0, 0, 0⟩⟩

instance : Inv Heis3 := ⟨fun p => ⟨-p.x, -p.y, -p.z + p.y * p.x⟩⟩

@[simp] theorem mul_x (p q : Heis3) : (p * q).x = p.x + q.x := rfl
@[simp] theorem mul_y (p q : Heis3) : (p * q).y = p.y + q.y := rfl
@[simp] theorem mul_z (p q : Heis3) : (p * q).z = p.z + q.z + p.y * q.x := rfl
@[simp] theorem one_x : (1 : Heis3).x = 0 := rfl
@[simp] theorem one_y : (1 : Heis3).y = 0 := rfl
@[simp] theorem one_z : (1 : Heis3).z = 0 := rfl
@[simp] theorem inv_x (p : Heis3) : p⁻¹.x = -p.x := rfl
@[simp] theorem inv_y (p : Heis3) : p⁻¹.y = -p.y := rfl
@[simp] theorem inv_z (p : Heis3) : p⁻¹.z = -p.z + p.y * p.x := rfl

instance : Fintype Heis3 :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3 × ZMod 3)
    { toFun := fun t => ⟨t.1, t.2.1, t.2.2⟩
      invFun := fun p => (p.x, p.y, p.z)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Group Heis3 where
  mul_assoc := by decide +kernel
  one_mul := by decide +kernel
  mul_one := by decide +kernel
  inv_mul_cancel := by decide +kernel

@[expose] def a₀ : Heis3 := ⟨0, 1, 0⟩

@[expose] def b₀ : Heis3 := ⟨1, 0, 0⟩

@[expose] def ζ₀ : Heis3 := ⟨0, 0, 1⟩

theorem card_Heis3 : Nat.card Heis3 = 27 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem commutator_mem : ∀ p q : Heis3, ∃ k : ZMod 3, ⁅p, q⁆ = ζ₀ ^ k.val := by decide +kernel

theorem commutator_a₀_b₀ : ∀ p : Heis3, ⁅p, a₀⁆ = ζ₀ ^ (-p.x).val ∧ ⁅p, b₀⁆ = ζ₀ ^ p.y.val := by
  decide +kernel

theorem exists_comm_eq :
    ∀ s t : ZMod 3, ∃ e : Heis3, ⁅e, a₀⁆ = ζ₀ ^ s.val ∧ ⁅e, b₀⁆ = ζ₀ ^ t.val := by
  decide +kernel

theorem eq_words_of_commutator_eq : ∀ u v : Heis3, ⁅u, v⁆ = ζ₀ →
    (∃ i j k : Fin 3, a₀ = u ^ (i : ℕ) * v ^ (j : ℕ) * ζ₀ ^ (k : ℕ)) ∧
    (∃ i j k : Fin 3, b₀ = u ^ (i : ℕ) * v ^ (j : ℕ) * ζ₀ ^ (k : ℕ)) := by
  decide +kernel

theorem card_commutator_eq : Fintype.card {q : Heis3 × Heis3 // ⁅q.1, q.2⁆ = ζ₀} = 216 := by
  decide +kernel

end Heis3

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg
