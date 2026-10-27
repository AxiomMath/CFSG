module

public import CFSG.GroupTheory.PCore.Defs
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
public import Mathlib.Order.CompletePartialOrder
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.SuzOddCore

open Subgroup
open scoped Pointwise

theorem orderOf_conj_eq {G : Type*} [Group G] (c x : G) : orderOf (c * x * c⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply]
  exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x

theorem exists_conj_mem_sylow_of_orderOf {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (P : Sylow p H) {y : H} (hy : orderOf y = p) :
    ∃ c : H, c * y * c⁻¹ ∈ (P : Subgroup H) := by
  have hcard : Nat.card (zpowers y) = p ^ 1 := by rw [Nat.card_zpowers, hy, pow_one]
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H Q P
  refine ⟨c, ?_⟩
  have hmem : y ∈ (Q : Subgroup H) := hQ (mem_zpowers y)
  have h1 : MulAut.conj c • y ∈ MulAut.conj c • (Q : Subgroup H) :=
    smul_mem_pointwise_smul _ _ _ hmem
  rwa [← Sylow.coe_subgroup_smul, hc, MulAut.smul_def, MulAut.conj_apply] at h1

theorem not_two_dvd_of_odd {N : Type*} [Group N] (hodd : Odd (Nat.card N)) :
    ¬ 2 ∣ Nat.card N := fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)

theorem oddCore_eq_bot_of_lines {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card E →
      ∃ P : Subgroup G, P ≤ E ∧ Nat.card P = p ^ (Nat.card E).factorization p ∧
        ∀ y ∈ P, orderOf y = p → ∃ x ∈ zpowers y, ∃ g ∈ E, ∃ k : ℕ,
          orderOf ((x * (g * x * g⁻¹)) ^ k) = 2) :
    CFSG.oddCore E = ⊥ := by
  refine sSup_eq_bot.2 fun N hN => ?_
  obtain ⟨hNn, hodd⟩ := hN
  by_contra hne
  have h1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hne
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt h1)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact not_two_dvd_of_odd hodd hpN
  have hpE : p ∣ Nat.card E := hpN.trans (Subgroup.card_subgroup_dvd_card N)
  obtain ⟨P, hPE, hPcard, hlines⟩ := h p hp hp2 hpE
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpN
  let PS : Sylow p E := Sylow.ofCard (P.subgroupOf E) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv, hPcard])
  have hyE : orderOf (y : E) = p := by rw [Subgroup.orderOf_coe, hy]
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow_of_orderOf PS hyE
  set y' : E := c * (y : E) * c⁻¹ with hy'
  have hyN : y' ∈ N := hNn.conj_mem _ y.2 c
  have hcP : (y' : G) ∈ P := by
    have : y' ∈ P.subgroupOf E := hc
    rwa [Subgroup.mem_subgroupOf] at this
  have hord : orderOf (y' : G) = p := by
    rw [Subgroup.orderOf_coe, hy', orderOf_conj_eq, hyE]
  obtain ⟨x, hx, g, hg, k, hk⟩ := hlines _ hcP hord
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
  let gE : E := ⟨g, hg⟩
  have hxN : y' ^ n ∈ N := N.zpow_mem hyN n
  have hwN : (y' ^ n * (gE * y' ^ n * gE⁻¹)) ^ k ∈ N :=
    N.pow_mem (N.mul_mem hxN (hNn.conj_mem _ hxN gE)) k
  have hw2 : orderOf ((y' ^ n * (gE * y' ^ n * gE⁻¹)) ^ k) = 2 := by
    rw [← Subgroup.orderOf_coe]
    simpa [gE] using hk
  have hN2 : orderOf (⟨_, hwN⟩ : N) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hw2
  exact not_two_dvd_of_odd hodd (hN2 ▸ orderOf_dvd_natCard _)

theorem even_orderOf_of_index_two {D : Type*} [Group D] [Finite D] {E : Subgroup D}
    (hE : E.index = 2) {n : D} (hn : n ∉ E) : Even (orderOf n) := by
  have key : ∀ k : ℕ, (n ^ k ∈ E ↔ Even k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Subgroup.mul_mem_iff_of_index_two hE, ih, Nat.even_add_one]
      simp [hn]
  rw [← key]
  rw [pow_orderOf_eq_one]
  exact E.one_mem

theorem oddCore_eq_bot_of_index_two {G : Type*} [Group G] [Finite G] {E D : Subgroup G}
    (hED : E ≤ D) (hidx : (E.subgroupOf D).index = 2) (hE : CFSG.oddCore E = ⊥) :
    CFSG.oddCore D = ⊥ := by
  refine sSup_eq_bot.2 fun N hN => ?_
  obtain ⟨hNn, hodd⟩ := hN
  have hNE : ∀ x ∈ N, (x : G) ∈ E := by
    intro x hx
    by_contra hxE
    have hx' : x ∉ E.subgroupOf D := by rwa [Subgroup.mem_subgroupOf]
    have hev := even_orderOf_of_index_two hidx hx'
    have hdvd : orderOf (⟨x, hx⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_coe] at hdvd
    exact not_two_dvd_of_odd hodd ((even_iff_two_dvd.1 hev).trans hdvd)
  let N' : Subgroup E := (N.map D.subtype).subgroupOf E
  have hN'n : N'.Normal := by
    constructor
    intro a ha b
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨x, hx, hxa⟩ := ha
    have hxa' : (x : G) = a := hxa
    refine ⟨⟨b, hED b.2⟩ * x * ⟨b, hED b.2⟩⁻¹, hNn.conj_mem x hx _, ?_⟩
    simp [hxa']
  have hcard : Nat.card N' = Nat.card N := by
    have h1 : N.map D.subtype ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      exact hNE x hx
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1).toEquiv,
      Subgroup.card_map_of_injective D.subtype_injective]
  have hN'bot : N' = ⊥ := eq_bot_iff.2 (hE ▸ le_sSup ⟨hN'n, hcard ▸ hodd⟩)
  have : Nat.card N = 1 := by rw [← hcard, hN'bot, Subgroup.card_bot]
  exact Subgroup.eq_bot_of_card_eq N this

theorem oddCore_eq_bot_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.oddCore A = ⊥) : CFSG.oddCore B = ⊥ := by
  refine sSup_eq_bot.2 fun N hN => ?_
  have hcard : Nat.card (N.comap e.toMonoidHom) = Nat.card N := by
    have := Subgroup.card_map_of_injective (K := N.comap e.toMonoidHom) (f := e.toMonoidHom)
      e.injective
    rw [Subgroup.map_comap_eq_self_of_surjective e.surjective] at this
    exact this.symm
  have hc : N.comap e.toMonoidHom = ⊥ :=
    eq_bot_iff.2 (h ▸ le_sSup ⟨hN.1.comap _, hcard ▸ hN.2⟩)
  have : Nat.card N = 1 := by rw [← hcard, hc, Subgroup.card_bot]
  exact Subgroup.eq_bot_of_card_eq N this

end CFSG.Sporadic.SuzOddCore
