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

namespace CFSG

namespace FiveTransitive.PermCentralizer

theorem support_le_compl_of_isCycle_of_commute_of_coprime_order
    {X : Type} [Fintype X] [DecidableEq X]
    {g v : Equiv.Perm X}
    (hg : g.IsCycle) (hcomm : Commute v g)
    (hcoprime : Nat.Coprime (orderOf v) (orderOf g)) :
    v.support ⊆ g.supportᶜ := by
  classical
  obtain ⟨hinvariant, hrmem⟩ := hg.commute_iff'.mp hcomm
  let r : Equiv.Perm g.support := v.subtypePerm hinvariant
  let c : Equiv.Perm g.support := g.subtypePermOfSupport
  have hrDvdV : orderOf r ∣ orderOf v := by
    apply orderOf_dvd_of_pow_eq_one
    ext x
    rw [Equiv.Perm.subtypePerm_apply_pow_of_mem hinvariant x.prop]
    simp
  have hcMap :
      (Equiv.Perm.ofSubtype :
        Equiv.Perm g.support →* Equiv.Perm X) c = g := by
    exact Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => Equiv.Perm.apply_mem_support)
      (fun _ => Equiv.Perm.mem_support.mpr)
  have hcOrder : orderOf c = orderOf g := by
    have horder := orderOf_injective
      (Equiv.Perm.ofSubtype :
        Equiv.Perm g.support →* Equiv.Perm X)
      Equiv.Perm.ofSubtype_injective c
    rw [hcMap] at horder
    exact horder.symm
  have hrDvdG : orderOf r ∣ orderOf g := by
    have horder :=
      (Subgroup.zpowers c).orderOf_dvd_natCard hrmem
    rw [Nat.card_zpowers, hcOrder] at horder
    exact horder
  have hrOrder : orderOf r = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime hrDvdV hrDvdG
  have hrOne : r = 1 := orderOf_eq_one_iff.mp hrOrder
  intro x hx
  rw [Finset.mem_compl]
  intro hxg
  apply Equiv.Perm.mem_support.mp hx
  have happly := DFunLike.congr_fun hrOne ⟨x, hxg⟩
  exact congrArg Subtype.val happly

end FiveTransitive.PermCentralizer

end CFSG
