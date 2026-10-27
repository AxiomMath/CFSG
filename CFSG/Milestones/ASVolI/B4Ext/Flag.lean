module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
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
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ASVolI

open Module

section Flag

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem burnsideB49x_exists_fixed_ne_zero (P : Subgroup (W ≃ₗ[ZMod 2] W)) (hP : IsPGroup 2 P)
    (h1 : 1 ≤ finrank (ZMod 2) W) : ∃ w : W, w ≠ 0 ∧ ∀ p ∈ P, p w = w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  have hdvd : 2 ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 (by omega)
  have h0 : (0 : W) ∈ MulAction.fixedPoints ↥P W := fun p => map_zero (p : W ≃ₗ[ZMod 2] W)
  obtain ⟨b, hb, hb0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hdvd h0
  exact ⟨b, fun h => hb0 h.symm, fun p hp => hb ⟨p, hp⟩⟩

@[expose, instance_reducible] noncomputable def burnsideB49x_quotAct (L : Submodule (ZMod 2) W)
    (P : Subgroup (W ≃ₗ[ZMod 2] W)) (hL : ∀ p ∈ P, ∀ x ∈ L, p x ∈ L) :
    MulAction ↥P (W ⧸ L) where
  smul p := L.mapQ L ((p : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (fun x hx => hL p p.2 x hx)
  one_smul x := by
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  mul_smul p q x := by
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

theorem burnsideB49x_exists_inv_two (P : Subgroup (W ≃ₗ[ZMod 2] W)) (hP : IsPGroup 2 P)
    (h2 : 2 ≤ finrank (ZMod 2) W) :
    ∃ Y : Submodule (ZMod 2) W, finrank (ZMod 2) Y = 2 ∧ ∀ p ∈ P, ∀ y ∈ Y, p y ∈ Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₁, hw₁0, hw₁⟩ := burnsideB49x_exists_fixed_ne_zero P hP (by omega)
  set L : Submodule (ZMod 2) W := Submodule.span (ZMod 2) {w₁} with hLdef
  have hL : ∀ p ∈ P, ∀ x ∈ L, p x ∈ L := by
    intro p hp x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul, hw₁ p hp]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w₁)
  letI := burnsideB49x_quotAct L P hL
  have hsmul : ∀ (p : ↥P) (x : W), (p • (Submodule.Quotient.mk x : W ⧸ L)) =
      Submodule.Quotient.mk ((p : W ≃ₗ[ZMod 2] W) x) := fun p x => rfl
  haveI : Finite (W ⧸ L) := Module.finite_of_finite (ZMod 2)
  have hLr : finrank (ZMod 2) L = 1 := finrank_span_singleton hw₁0
  have hdvd : 2 ∣ Nat.card (W ⧸ L) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have := Submodule.finrank_quotient_add_finrank L
    exact dvd_pow_self 2 (by omega)
  have h0 : (0 : W ⧸ L) ∈ MulAction.fixedPoints ↥P (W ⧸ L) := fun p => by
    change L.mapQ L _ _ 0 = 0
    exact map_zero _
  obtain ⟨b, hb, hb0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (W ⧸ L) hdvd h0
  obtain ⟨w₂, rfl⟩ := Submodule.Quotient.mk_surjective L b
  have hw₂ : w₂ ∉ L := fun h => hb0 ((Submodule.Quotient.mk_eq_zero L).2 h).symm
  have hfix : ∀ p ∈ P, (p : W ≃ₗ[ZMod 2] W) w₂ - w₂ ∈ L := by
    intro p hp
    have := hb ⟨p, hp⟩
    rw [hsmul] at this
    exact (Submodule.Quotient.eq L).1 this
  refine ⟨Submodule.span (ZMod 2) {w₁, w₂}, ?_, ?_⟩
  · have hind : LinearIndependent (ZMod 2) ![w₁, w₂] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        rw [zero_smul, add_zero] at hst
        exact ⟨(smul_eq_zero.1 hst).resolve_right hw₁0, rfl⟩
      · exfalso
        have ht1 : t = 1 := CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_one_of_ne_zero ht
        subst ht1
        apply hw₂
        rw [one_smul] at hst
        have : w₂ = -(s • w₁) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hst
        rw [this]
        exact L.neg_mem (L.smul_mem s (Submodule.mem_span_singleton_self w₁))
    have := finrank_span_eq_card hind
    rw [Matrix.range_cons_cons_empty] at this
    simpa using this
  · intro p hp y hy
    obtain ⟨a, c, rfl⟩ := Submodule.mem_span_pair.1 hy
    rw [map_add, map_smul, map_smul, hw₁ p hp]
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 (hfix p hp)
    have : (p : W ≃ₗ[ZMod 2] W) w₂ = d • w₁ + w₂ := by rw [hd]; abel
    rw [this, Submodule.mem_span_pair]
    exact ⟨a + c * d, c, by rw [smul_add, smul_smul, add_smul]; abel⟩

end Flag

end CFSG.ASVolI
