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

namespace CFSG.Quasithin.H.Trio

abbrev invSubAction {G α : Type*} [Group G] [MulAction G α] (P : Subgroup G) (X : Finset α)
    (hinv : ∀ g ∈ P, ∀ x ∈ X, g • x ∈ X) : MulAction P {x : α // x ∈ X} where
  smul p x := ⟨(p : G) • x.1, hinv p p.2 x.1 x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul p q x := Subtype.ext (mul_smul (p : G) (q : G) x.1)

theorem exists_common_fixed {G α : Type*} [Group G] [MulAction G α] {P : Subgroup G}
    (hP : IsPGroup 2 P) (X : Finset α) (hX : X.card = 3)
    (hinv : ∀ g ∈ P, ∀ x ∈ X, g • x ∈ X) : ∃ x ∈ X, ∀ g ∈ P, g • x = x := by
  letI : MulAction P {x : α // x ∈ X} := invSubAction P X hinv
  have hcard : Nat.card {x : α // x ∈ X} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hX]
  have hmod := hP.card_modEq_card_fixedPoints {x : α // x ∈ X}
  rw [hcard] at hmod
  have hpos : Nat.card (MulAction.fixedPoints P {x : α // x ∈ X}) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact absurd hmod (by decide)
  obtain ⟨y⟩ := (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hpos)).1
  have hy := MulAction.mem_fixedPoints.1 y.2
  refine ⟨y.1.1, y.1.2, fun g hg => ?_⟩
  exact congrArg Subtype.val (hy ⟨g, hg⟩)

end CFSG.Quasithin.H.Trio
