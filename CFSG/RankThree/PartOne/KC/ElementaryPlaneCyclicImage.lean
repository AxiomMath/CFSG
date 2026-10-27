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

namespace CFSG.RankThree.PartOne

theorem card_ker_eq_prime_of_ne_one {A C : Type*} [Group A] [Finite A] [Group C] [IsCyclic C]
    {p : ℕ} (hp : p.Prime) (hApow : ∀ x : A, x ^ p = 1) (hAcard : Nat.card A = p ^ 2)
    (π : A →* C) (hπ : π ≠ 1) : Nat.card π.ker = p ∧ Nat.card π.range = p := by
  have hk := Subgroup.card_ker_mul_card_range π
  have hexp : Monoid.exponent π.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    obtain ⟨a, ha⟩ := g.2
    refine Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← ha, ← map_pow, hApow, map_one]
  have hcyc : IsCyclic π.range := inferInstance
  have hdvd : Nat.card π.range ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact hexp
  have hne : Nat.card π.range ≠ 1 := by
    intro h1
    apply hπ
    have : π.range = ⊥ := (Subgroup.card_eq_one).mp h1
    exact MonoidHom.range_eq_bot_iff.mp this
  have hr : Nat.card π.range = p := ((Nat.dvd_prime hp).mp hdvd).resolve_left hne
  refine ⟨?_, hr⟩
  rw [hr, hAcard, sq] at hk
  exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [hk])

end CFSG.RankThree.PartOne
