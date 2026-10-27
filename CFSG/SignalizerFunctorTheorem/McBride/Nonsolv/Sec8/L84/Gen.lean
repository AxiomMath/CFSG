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

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L84

variable {G : Type*} [Group G]

theorem eq_of_forall_coprime_relIndex [Finite G] {N X : Subgroup G} (hXN : X ≤ N)
    (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card N → ∃ P : Subgroup G, P ≤ X ∧
      Nat.Coprime (P.relIndex N) r) : X = N := by
  by_contra hne
  have hidx : (X.subgroupOf N).index ≠ 1 := by
    intro h1
    refine hne (le_antisymm hXN ?_)
    exact Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h1)
  obtain ⟨r, hr, hdvd⟩ := Nat.exists_prime_and_dvd hidx
  obtain ⟨P, hPX, hcop⟩ := h r hr (hdvd.trans (Subgroup.index_dvd_card _))
  have hle : P.subgroupOf N ≤ X.subgroupOf N := Subgroup.comap_mono hPX
  have h2 : r ∣ (P.subgroupOf N).index := hdvd.trans (Subgroup.index_dvd_of_le hle)
  exact hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm h2)

end L84

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
