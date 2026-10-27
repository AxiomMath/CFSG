module

public import CFSG.Permutation.FiveTransitive.Degree68SevenSmallFiber
public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore
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

namespace CFSG

namespace FiveTransitive.Degree68ThreeBoundCore
open MulAction SylowFixedActionCore

theorem card_eq_three_of_triple
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hkill : ∀ R : Subgroup P, IsPGroup 3 R →
      6 ≤ Nat.card (fixedPoints R X) → Nat.card R = 1)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q)
    (hcommon : Nat.card (fixedPoints Q X) = 5)
    (x : X) (hx : Nat.card (orbit Q x) = 3) : Nat.card Q = 3 := by
  classical
  let T := stabilizer Q x
  let R := T.map Q.subtype
  have hR : IsPGroup 3 R := (hQ.to_subgroup T).map Q.subtype
  have hxF : x ∉ fixedPoints Q X := by
    intro h
    have hh := mem_fixedPoints_iff_card_orbit_eq_one.mp h
    rw [← Nat.card_eq_fintype_card,hx] at hh
    omega
  have hsub : insert x (fixedPoints Q X) ⊆ fixedPoints R X := by
    intro y hy r
    obtain ⟨q,hq,hqr⟩ := r.property
    change Q.subtype q = r.val at hqr
    rcases Set.mem_insert_iff.mp hy with hy | hy
    · subst y
      change r.val • x = x
      rw [← hqr]
      exact hq
    · change r.val • y = y
      rw [← hqr]
      exact hy q
  have hRfixed : 6 ≤ Nat.card (fixedPoints R X) := by
    have hh := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem hxF,← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq,hcommon] at hh
    omega
  have hRone := hkill R hR hRfixed
  have hTcard : Nat.card T = Nat.card R := Nat.card_congr
    (T.equivMapOfInjective Q.subtype Subtype.val_injective).toEquiv
  have hm := card_orbit_mul_card_stabilizer_eq_card_group Q x
  simp only [← Nat.card_eq_fintype_card] at hm
  change Nat.card (orbit Q x) * Nat.card T = Nat.card Q at hm
  rw [hx,hTcard,hRone,mul_one] at hm
  exact hm.symm

end FiveTransitive.Degree68ThreeBoundCore

end CFSG
