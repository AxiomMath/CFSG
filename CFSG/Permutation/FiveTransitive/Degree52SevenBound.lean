module

public import Mathlib.Tactic.NormNum.Prime
import CFSG.Permutation.FiveTransitive.Degree52PrimeTupleDivisibility
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

namespace FiveTransitive.Degree52SevenBound

open MulAction

theorem card_le_three_hundred_forty_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 7 Q)
    (hfixed : Nat.card (fixedPoints Q X) = 10) : Nat.card Q ≤ 343 := by
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hd := FiveTransitive.Degree52PrimeTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q 17 (by omega)
  rw [hfixed] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he3 : e ≤ 3 := by
    by_contra hn
    have h2401 : 2401 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 7 (by omega : 4 ≤ e)
    have hh := h2401.trans hd
    norm_num at hh
  rw [he]
  exact Nat.pow_le_pow_right (by norm_num : 0 < 7) he3

theorem card_le_seven_of_fixed_twenty_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 7 Q)
    (hfixed : Nat.card (fixedPoints Q X) = 24) : Nat.card Q ≤ 7 := by
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hd := FiveTransitive.Degree52PrimeTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q 3 (by omega)
  rw [hfixed] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he1 : e ≤ 1 := by
    by_contra hn
    have h49 : 49 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 7 (by omega : 2 ≤ e)
    have hh := h49.trans hd
    norm_num at hh
  rw [he]
  exact Nat.pow_le_pow_right (by norm_num : 0 < 7) he1

end FiveTransitive.Degree52SevenBound

end CFSG
