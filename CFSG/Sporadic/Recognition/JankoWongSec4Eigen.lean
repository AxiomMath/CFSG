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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Sporadic.Recognition.JankoWong

variable {G : Type*} [Group G]

@[expose] def negSub (N : Subgroup G) (z : G) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) :
    Subgroup G where
  carrier := {n | n ∈ N ∧ z * n * z⁻¹ = n⁻¹}
  one_mem' := ⟨N.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hza⟩ ⟨hb, hzb⟩
    refine ⟨N.mul_mem ha hb, ?_⟩
    rw [← conj_mul, hza, hzb, ← mul_inv_rev, hN b hb a ha]
  inv_mem' := by
    rintro a ⟨ha, hza⟩
    refine ⟨N.inv_mem ha, ?_⟩
    rw [← conj_inv, hza]

theorem mem_negSub {N : Subgroup G} {z : G} {hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x} {x : G} :
    x ∈ negSub N z hN ↔ x ∈ N ∧ z * x * z⁻¹ = x⁻¹ :=
  Iff.rfl

theorem negSub_le (N : Subgroup G) (z : G) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) :
    negSub N z hN ≤ N :=
  fun _ hx => hx.1

theorem exists_decomp (N : Subgroup G) (z : G) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hN3 : ∀ x ∈ N, x ^ 3 = 1) (hz2 : z ^ 2 = 1) (hzN : ∀ x ∈ N, z * x * z⁻¹ ∈ N) :
    ∀ n ∈ N, ∃ p ∈ N, z * p * z⁻¹ = p ∧ ∃ q ∈ negSub N z hN, n = p * q := by
  intro n hn
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hmN : z * n * z⁻¹ ∈ N := hzN n hn
  have hnm : n * (z * n * z⁻¹) = (z * n * z⁻¹) * n := hN n hn _ hmN
  have hzm : z * (z * n * z⁻¹) * z⁻¹ = n := by
    rw [hzi]
    calc z * (z * n * z) * z = z * z * n * (z * z) := by group
      _ = n := by rw [hzz]; simp
  have hprod : ∀ m : G, n * m = m * n → (n * m)⁻¹ * (n * m⁻¹)⁻¹ = n := by
    intro m hm
    calc (n * m)⁻¹ * (n * m⁻¹)⁻¹ = m⁻¹ * (n⁻¹ * m) * n⁻¹ := by group
      _ = m⁻¹ * (m * n⁻¹) * n⁻¹ := by rw [(Commute.inv_left (show Commute n m from hm)).eq]
      _ = n⁻¹ * n⁻¹ := by group
      _ = n⁻¹ * n⁻¹ * n ^ 3 := by rw [hN3 n hn, mul_one]
      _ = n := by group
  refine ⟨(n * (z * n * z⁻¹))⁻¹, N.inv_mem (N.mul_mem hn hmN), ?_,
    (n * (z * n * z⁻¹)⁻¹)⁻¹, ⟨N.inv_mem (N.mul_mem hn (N.inv_mem hmN)), ?_⟩,
    (hprod _ hnm).symm⟩
  · rw [← conj_inv, ← conj_mul, hzm, ← hnm]
  · rw [← conj_inv, ← conj_mul, ← conj_inv, hzm]
    simp

theorem inf_eq_bot (N : Subgroup G) (z : G) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hN3 : ∀ x ∈ N, x ^ 3 = 1) :
    (N ⊓ Subgroup.centralizer ({z} : Set G)) ⊓ negSub N z hN = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxA, hxneg⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.1 hxA
  have hxz := (mem_negSub.1 hxneg).2
  rw [Subgroup.mem_centralizer_singleton_iff] at hxC
  have hxz' : z * x * z⁻¹ = x := by rw [← hxC]; simp
  have hxinv : x = x⁻¹ := hxz'.symm.trans hxz
  have hx2 : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [← hxinv]
      _ = 1 := mul_inv_cancel x
  calc x = x * x * x := by rw [hx2, one_mul]
    _ = x ^ 3 := (pow_three' x).symm
    _ = 1 := hN3 x hxN

theorem card_eq [Finite G] (N : Subgroup G) (z : G) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hN3 : ∀ x ∈ N, x ^ 3 = 1) (hz2 : z ^ 2 = 1) (hzN : ∀ x ∈ N, z * x * z⁻¹ ∈ N) :
    Nat.card N = Nat.card ↥(N ⊓ Subgroup.centralizer ({z} : Set G)) *
      Nat.card ↥(negSub N z hN) := by
  let f : ↥(N ⊓ Subgroup.centralizer ({z} : Set G)) × ↥(negSub N z hN) → N := fun pq =>
    ⟨pq.1 * pq.2, N.mul_mem (Subgroup.mem_inf.1 pq.1.2).1 (negSub_le N z hN pq.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩ h
      have h' : p * q = p' * q' := congrArg Subtype.val h
      have e : p'⁻¹ * p = q' * q⁻¹ := by
        calc p'⁻¹ * p = p'⁻¹ * (p * q) * q⁻¹ := by group
          _ = p'⁻¹ * (p' * q') * q⁻¹ := by rw [h']
          _ = q' * q⁻¹ := by group
      have hmem : p'⁻¹ * p ∈ (N ⊓ Subgroup.centralizer ({z} : Set G)) ⊓ negSub N z hN :=
        Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hp') hp, e ▸ mul_mem hq' (inv_mem hq)⟩
      rw [inf_eq_bot N z hN hN3, Subgroup.mem_bot] at hmem
      have hp1 : p' = p := inv_mul_eq_one.1 hmem
      have hq1 : q' = q := mul_inv_eq_one.1 (e ▸ hmem)
      subst hp1 hq1
      rfl
    · rintro ⟨n, hn⟩
      obtain ⟨p, hpN, hpz, q, hq, hnpq⟩ := exists_decomp N z hN hN3 hz2 hzN n hn
      refine ⟨(⟨p, Subgroup.mem_inf.2 ⟨hpN, ?_⟩⟩, ⟨q, hq⟩), Subtype.ext hnpq.symm⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc p * z = z * p * z⁻¹ * z := by rw [hpz]
        _ = z * p := by group
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective f hf).symm

end CFSG.Sporadic.Recognition.JankoWong
