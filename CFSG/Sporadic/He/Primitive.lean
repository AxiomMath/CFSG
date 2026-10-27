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
public import Mathlib.GroupTheory.GroupAction.Primitive
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

namespace CFSG.Sporadic.He

open Pointwise

theorem isPreprimitive_of_suborbit_labels_witness
    {G X : Type*} [Group G] [MulAction G X] [Fintype X] [DecidableEq X]
    [MulAction.IsPretransitive G X] (x : X) (H : Subgroup G)
    (hH : ∀ h ∈ H, h • x = x) {k : ℕ} (lab : X → Fin k)
    (horb : ∀ p q : X, lab p = lab q → ∃ h ∈ H, h • p = q)
    (hdiv : ∀ S : Finset (Fin k), lab x ∈ S →
      (∑ i ∈ S, (Finset.univ.filter (fun p => lab p = i)).card) ∣ Fintype.card X →
      S = {lab x} ∨ S = Finset.univ ∨
        ∃ g : G, ∃ y : X, lab y ∈ S ∧ lab (g • x) ∈ S ∧ lab (g • y) ∉ S) :
    MulAction.IsPreprimitive G X := by
  classical
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base x fun {B} hxB hB => ?_
  have hclosed : ∀ p q : X, p ∈ B → lab p = lab q → q ∈ B := by
    intro p q hp hpq
    obtain ⟨h, hh, rfl⟩ := horb p q hpq
    have hhx : h • x ∈ B := by
      rw [hH h hh]
      exact hxB
    rw [← hB.smul_eq_of_mem hxB hhx]
    exact Set.smul_mem_smul_set hp
  let S : Finset (Fin k) := (Finset.univ.filter (· ∈ B)).image lab
  have hmemS : ∀ p, lab p ∈ S ↔ p ∈ B := by
    intro p
    constructor
    · intro hp
      obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
      exact hclosed q p (Finset.mem_filter.mp hq).2 hqp
    · intro hp
      exact Finset.mem_image_of_mem lab (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩)
  have hBS : B = ↑(Finset.univ.filter fun p => lab p ∈ S) := by
    ext p
    rw [Finset.mem_coe, Finset.mem_filter, hmemS]
    exact ⟨fun hp => ⟨Finset.mem_univ p, hp⟩, fun hp => hp.2⟩
  have hdvd : (∑ i ∈ S, (Finset.univ.filter (fun p => lab p = i)).card) ∣ Fintype.card X := by
    rw [Finset.sum_card_fiberwise_eq_card_filter, ← Set.ncard_coe_finset, ← hBS,
      ← Nat.card_eq_fintype_card]
    exact hB.ncard_dvd_card ⟨x, hxB⟩
  rcases hdiv S ((hmemS x).mpr hxB) hdvd with hS | hS | ⟨g, y, hy, hgx, hgy⟩
  · left
    have hx : ∀ r ∈ B, r = x := by
      intro r hr
      have hr' : lab r ∈ S := (hmemS r).mpr hr
      rw [hS, Finset.mem_singleton] at hr'
      obtain ⟨h, hh, hhr⟩ := horb x r hr'.symm
      rw [← hhr, hH h hh]
    intro p hp q hq
    rw [hx p hp, hx q hq]
  · right
    ext p
    refine ⟨fun _ => Set.mem_univ p, fun _ => (hmemS p).mp ?_⟩
    rw [hS]
    exact Finset.mem_univ (lab p)
  · exfalso
    have hgB : g • B = B := hB.smul_eq_of_mem hxB ((hmemS _).1 hgx)
    have hgyB : g • y ∈ B := by
      rw [← hgB]
      exact Set.smul_mem_smul_set ((hmemS y).1 hy)
    exact hgy ((hmemS _).2 hgyB)

end CFSG.Sporadic.He
