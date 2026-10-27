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

namespace CFSG.RankThree.PartOne.KFSU5

variable {V : Type*} [Group V] [Finite V]

theorem exists_orderOf_eq_normalizer_sylow (N : Subgroup V) [N.Normal] {p r : ℕ} [Fact p.Prime]
    [Fact r.Prime] (S : Sylow r N) (hp : p ∣ Nat.card (V ⧸ N)) :
    ∃ x : V, orderOf x = p ∧
      x ∈ Subgroup.normalizer (((S : Subgroup N).map N.subtype : Subgroup V) : Set V) := by
  set H : Subgroup V := Subgroup.normalizer (((S : Subgroup N).map N.subtype : Subgroup V) : Set V)
    with hH
  have hsup : H ⊔ N = ⊤ := Sylow.normalizer_sup_eq_top S
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp H.subtype) := by
    intro y
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hv : v ∈ H ⊔ N := by rw [hsup]; exact Subgroup.mem_top v
    obtain ⟨a, ha, n, hn, hv'⟩ := Subgroup.mem_sup_of_normal_right.mp hv
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [← hv']
    exact (QuotientGroup.eq.mpr (by simpa using N.inv_mem hn)).symm
  have hdvd : p ∣ Nat.card H := hp.trans (Subgroup.card_dvd_of_surjective hsurj)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H) p hdvd
  exact ⟨y.1, by rw [Subgroup.orderOf_coe, hy], y.2⟩

theorem exists_orderOf_eq_normalizer_sylow_of_pow (N : Subgroup V) [N.Normal] {p r : ℕ}
    [hp : Fact p.Prime] [Fact r.Prime] (S : Sylow r N) {e : V} (hep : e ^ p = 1) (heN : e ∉ N) :
    ∃ x : V, orderOf x = p ∧
      x ∈ Subgroup.normalizer (((S : Subgroup N).map N.subtype : Subgroup V) : Set V) := by
  refine exists_orderOf_eq_normalizer_sylow N S ?_
  have h1 : ((e : V ⧸ N)) ^ p = 1 := by rw [← QuotientGroup.mk_pow, hep, QuotientGroup.mk_one]
  have h2 : ((e : V ⧸ N)) ≠ 1 := fun h => heN ((QuotientGroup.eq_one_iff e).mp h)
  rw [← orderOf_eq_prime h1 h2]
  exact orderOf_dvd_natCard _

end CFSG.RankThree.PartOne.KFSU5
