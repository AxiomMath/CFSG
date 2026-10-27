module

public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeOrbitRigidity
public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeOrbitFamily
public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeOrbitSize
public import CFSG.Permutation.FiveTransitive.NormalizerExteriorOrbitFamily
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG

namespace FiveTransitive.Degree80LargePrimeSupport
open MulAction

theorem support_le_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpl : 11 ≤ p)
    (hpq : p.Coprime q) (hqpred : ¬ q ∣ p - 1)
    (Q : Subgroup P) (hQ : IsPGroup p Q)
    (hgap : 80 < p * q + Nat.card (fixedPoints Q X))
    (z : Subgroup.normalizer (Q : Set P)) (hz : z ^ q = 1) :
    z.val.val.support.card ≤ Nat.card (fixedPoints Q X) := by
  classical
  have hn : Nat.card X < p ^ 2 := by
    rw [Nat.card_eq_fintype_card,hcard]
    nlinarith
  have hfamily : Nat.card (NormalizerOrbitFamily.Family (X := X) Q p) < q := by
    have hh := NormalizerExteriorOrbitFamily.card_mul_add_fixed_le (X := X) Q p (by omega)
    rw [Nat.card_eq_fintype_card (α := X),hcard] at hh
    by_contra hnq
    have hmul := Nat.mul_le_mul_right p
      (show q ≤ Nat.card (NormalizerOrbitFamily.Family (X := X) Q p) by omega)
    nlinarith
  have hfix (x : X) (hx : x ∉ fixedPoints Q X) : z.val • x = x := by
    have ho := Degree72LargePrimeOrbitSize.card_eq_prime p hp hQ hn x hx
    let O : NormalizerOrbitFamily.Family (X := X) Q p :=
      ⟨Quotient.mk'' x,by simpa only [orbitRel.Quotient.orbit_mk] using ho⟩
    have he := Degree72LargePrimeOrbitFamily.prime_fixes_family q hq Q p hfamily z hz O
    have horbit : z.val • x ∈ orbit Q x := Quotient.exact he
    exact Degree72LargePrimeOrbitRigidity.fixes_preserved_orbit p q hp hq hpq hqpred
      Q hQ z.val z.property (congrArg Subtype.val hz) x ho.le horbit x (mem_orbit_self x)
  have hsub : (z.val.val.support : Set X) ⊆ fixedPoints Q X := by
    intro x hx
    by_contra hn
    exact (Equiv.Perm.mem_support.mp hx) (hfix x hn)
  have hh := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset,← Nat.card_coe_set_eq] at hh
  exact hh

end FiveTransitive.Degree80LargePrimeSupport

end CFSG
