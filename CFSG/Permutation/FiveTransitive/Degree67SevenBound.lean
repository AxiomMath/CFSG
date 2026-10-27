module

public import Mathlib.Tactic.NormNum.Prime
import CFSG.Permutation.FiveTransitive.Degree67LargePrimeTupleDivisibility
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
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
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
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG

namespace FiveTransitive.Degree67SevenBound

open MulAction

theorem card_le_seven_pow_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 7 Q)
    (hfixed : Nat.card (fixedPoints Q X) = 11) : Nat.card Q ≤ 16807 := by
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hd := FiveTransitive.Degree67LargePrimeTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q 23 (by omega)
  rw [hfixed] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he5 : e ≤ 5 := by
    by_contra hn
    have h117649 : 117649 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 7 (by omega : 6 ≤ e)
    have hh := h117649.trans hd
    norm_num at hh
  rw [he]
  exact Nat.pow_le_pow_right (by norm_num : 0 < 7) he5

end FiveTransitive.Degree67SevenBound

end CFSG
