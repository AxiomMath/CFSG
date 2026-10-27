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

namespace CFSG.Quasithin.J4Loc

variable {G : Type*} [Group G]

theorem card_mul_card_le [Finite G] {A X Y : Subgroup G} (hX : X ≤ A) (hY : Y ≤ A) :
    Nat.card X * Nat.card Y ≤ Nat.card A * Nat.card ↥(X ⊓ Y) := by
  have h1 := Subgroup.relIndex_mul_card (H := X) (K := A)
  have h2 := Subgroup.relIndex_mul_card (H := Y) (K := A)
  have h3 := Subgroup.relIndex_mul_card (H := X ⊓ Y) (K := A)
  have h4 := Subgroup.relIndex_inf_le (H := X) (K := Y) (L := A)
  rw [inf_eq_left.2 hX] at h1
  rw [inf_eq_left.2 hY] at h2
  rw [inf_eq_left.2 (inf_le_left.trans hX)] at h3
  have ha : 0 < Nat.card A := Nat.card_pos
  have hrz : 0 < (X ⊓ Y).relIndex A := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, zero_mul] at h3
    omega
  have h5 : Nat.card X * Nat.card Y * (X ⊓ Y).relIndex A ≤
      Nat.card A * Nat.card ↥(X ⊓ Y) * (X ⊓ Y).relIndex A := by
    calc Nat.card X * Nat.card Y * (X ⊓ Y).relIndex A
        ≤ Nat.card X * Nat.card Y * (X.relIndex A * Y.relIndex A) :=
          Nat.mul_le_mul_left _ h4
      _ = (X.relIndex A * Nat.card X) * (Y.relIndex A * Nat.card Y) := by ring
      _ = Nat.card A * Nat.card A := by rw [h1, h2]
      _ = Nat.card A * ((X ⊓ Y).relIndex A * Nat.card ↥(X ⊓ Y)) := by rw [h3]
      _ = Nat.card A * Nat.card ↥(X ⊓ Y) * (X ⊓ Y).relIndex A := by ring
  exact Nat.le_of_mul_le_mul_right h5 hrz

@[expose] def cmp (n : G) (C : Subgroup G) : Subgroup G where
  carrier := {y | n⁻¹ * y * n ∈ C}
  mul_mem' := fun {a b} ha hb => by
    have : n⁻¹ * (a * b) * n = (n⁻¹ * a * n) * (n⁻¹ * b * n) := by group
    show n⁻¹ * (a * b) * n ∈ C
    rw [this]
    exact C.mul_mem ha hb
  one_mem' := by
    show n⁻¹ * 1 * n ∈ C
    simp
  inv_mem' := fun {a} ha => by
    have : n⁻¹ * a⁻¹ * n = (n⁻¹ * a * n)⁻¹ := by group
    show n⁻¹ * a⁻¹ * n ∈ C
    rw [this]
    exact C.inv_mem ha

theorem card_cmp (n : G) (C : Subgroup G) : Nat.card (cmp n C) = Nat.card C := by
  refine Nat.card_congr
    { toFun := fun y => ⟨n⁻¹ * y.1 * n, y.2⟩
      invFun := fun c => ⟨n * c.1 * n⁻¹, by
        show n⁻¹ * (n * c.1 * n⁻¹) * n ∈ C
        have : n⁻¹ * (n * c.1 * n⁻¹) * n = c.1 := by group
        rw [this]
        exact c.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun c => Subtype.ext (by simp [mul_assoc]) }

end CFSG.Quasithin.J4Loc
