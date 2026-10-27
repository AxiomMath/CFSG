module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.RankThree.PartOne.Mult

open Subgroup

def centralTorsion (K : Type*) [Group K] (m : ℕ) : Subgroup K where
  carrier := {x | x ∈ center K ∧ x ^ m = 1}
  mul_mem' := by
    rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
    refine ⟨mul_mem hx hy, ?_⟩
    have hc : Commute x y := mem_center_iff.mp hy x
    rw [hc.mul_pow, hxm, hym, one_mul]
  one_mem' := ⟨one_mem _, one_pow m⟩
  inv_mem' := by
    rintro x ⟨hx, hxm⟩
    exact ⟨inv_mem hx, by rw [inv_pow, hxm, inv_one]⟩

theorem mem_centralTorsion {K : Type*} [Group K] {m : ℕ} {x : K} :
    x ∈ centralTorsion K m ↔ x ∈ center K ∧ x ^ m = 1 := Iff.rfl

theorem exists_central_p_complement {K : Type*} [Group K] [Finite K] (p : ℕ) [hp : Fact p.Prime] :
    ∃ N : Subgroup K, N ≤ center K ∧ ¬ p ∣ Nat.card N ∧
      ∀ z ∈ center K, ∃ n : ℕ, z ^ p ^ n ∈ N := by
  obtain ⟨e, m, hm, hcard⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.card_pos (α := center K)).ne' p hp.out.ne_one
  refine ⟨centralTorsion K m, fun x hx => hx.1, ?_, fun z hz => ⟨e, pow_mem hz _, ?_⟩⟩
  · intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have h1 : (x : K) ^ m = 1 := x.2.2
    have h2 : orderOf (x : K) = p := by rw [Subgroup.orderOf_coe]; exact hx
    exact hm (h2 ▸ orderOf_dvd_of_pow_eq_one h1)
  · have hz1 : z ^ Nat.card (center K) = 1 := by
      have := pow_card_eq_one' (G := center K) (x := ⟨z, hz⟩)
      exact congrArg Subtype.val this
    rw [← pow_mul, ← hcard]
    exact hz1

theorem exists_central_p_extension {K : Type*} [Group K] [Finite K] [Group.IsPerfect K] {p : ℕ}
    [Fact p.Prime] (hpZ : p ∣ Nat.card (center K)) :
    ∃ (N : Subgroup K) (_ : N.Normal) (π : K ⧸ N →* K ⧸ center K),
      Group.IsPerfect (K ⧸ N) ∧ (∀ k : K, π (QuotientGroup.mk k) = QuotientGroup.mk k) ∧
        Function.Surjective π ∧ π.ker ≤ center (K ⧸ N) ∧ IsPGroup p π.ker ∧ π.ker ≠ ⊥ := by
  obtain ⟨N, hNZ, hNp, hNpow⟩ := exists_central_p_complement (K := K) p
  have hNn : N.Normal := normal_of_le_center hNZ
  refine ⟨N, hNn, QuotientGroup.map N (center K) (MonoidHom.id K) (fun n hn => hNZ hn),
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N), fun k => rfl, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk k, rfl⟩
  · intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have hk : k ∈ center K := by
      have : (QuotientGroup.mk k : K ⧸ center K) = 1 := hx
      exact (QuotientGroup.eq_one_iff k).mp this
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hk g]
  · intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective x.1
    have hxk : (QuotientGroup.mk k : K ⧸ center K) = 1 := by
      have := x.2
      rw [MonoidHom.mem_ker] at this
      rw [← hk] at this
      exact this
    obtain ⟨n, hn⟩ := hNpow k ((QuotientGroup.eq_one_iff k).mp hxk)
    refine ⟨n, Subtype.ext ?_⟩
    change x.1 ^ p ^ n = 1
    rw [← hk, ← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hn
  · intro hbot
    have hnle : ¬ center K ≤ N := fun hle => hNp (hpZ.trans (card_dvd_of_le hle))
    obtain ⟨z, hz, hzN⟩ := Set.not_subset.mp hnle
    have hmem : (QuotientGroup.mk z : K ⧸ N) ∈ (QuotientGroup.map N (center K) (MonoidHom.id K)
        (fun n hn => hNZ hn)).ker := by
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff z).mpr hz
    rw [hbot, mem_bot] at hmem
    exact hzN ((QuotientGroup.eq_one_iff z).mp hmem)

theorem coprime_six_card_of_isPGroup {G : Type*} [Group G] [Finite G] {H : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hH : IsPGroup p H) : Nat.Coprime (Nat.card H) 6 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  rw [hk]
  refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_)
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem odd_card_of_isPGroup {G : Type*} [Group G] [Finite G] {H : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hH : IsPGroup p H) : Odd (Nat.card H) :=
  Nat.coprime_two_right.mp
    (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) (coprime_six_card_of_isPGroup hp hp3 hH))

end CFSG.RankThree.PartOne.Mult
