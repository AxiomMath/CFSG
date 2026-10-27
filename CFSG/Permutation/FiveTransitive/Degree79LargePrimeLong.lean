module

public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan
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

namespace FiveTransitive.Degree79LargePrimeLong

open MulAction

theorem long_not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Finset X) (hs : s.card = 5) (p : ℕ) (hp : p.Prime) (hlarge : 41 ≤ p) :
    ¬ p ∣ Nat.card (fixingSubgroup P (s : Set X)) := by
  intro hd
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' p hd
  let g : Equiv.Perm X := (u : P)
  have hg : orderOf g = p := (Subgroup.orderOf_coe (u : P)).trans
    ((Subgroup.orderOf_coe u).trans hu)
  have hsupport : g.support.card ≤ 74 := by
    have hsub : g.support ⊆ sᶜ := by
      intro x hx
      apply Finset.mem_compl.mpr
      intro hxs
      exact (Equiv.Perm.mem_support.mp hx)
        ((mem_fixingSubgroup_iff P).mp u.property x hxs)
    have h := Finset.card_le_card hsub
    rw [Finset.card_compl,hcard,hs] at h
    exact h
  have hcycle : g.IsCycle := Equiv.Perm.isCycle_of_prime_order (by rwa [hg]) (by rw [hg]; omega)
  have hsupp : g.support.card = p := by rw [← hcycle.orderOf,hg]
  have h2 : IsMultiplyPretransitive P X 2 := by
    let _ := h5
    exact isMultiplyPretransitive_of_le (G := P) (α := X) (n := 5) (by omega) (by rw [Nat.card_eq_fintype_card,hcard]; omega)
  have hprim := isPreprimitive_of_is_two_pretransitive h2
  apply hnotAlt
  apply OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    hprim hp (by rw [Nat.card_eq_fintype_card,hcard]; omega) hcycle hsupp
  exact (u : P).property

end FiveTransitive.Degree79LargePrimeLong

end CFSG
