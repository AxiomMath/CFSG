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

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem aux_IndexArg_subtype_pow_eq_one {G : Type*} [Group G] (H : Subgroup G) (x : H) (n : ℕ)
    (h : (x : G) ^ n = 1) : x ^ n = 1 := by
  apply Subtype.ext
  simpa using h

theorem aux_IndexArg_mk'_eq_one_iff {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (x : G) :
    QuotientGroup.mk' N x = 1 ↔ x ∈ N :=
  QuotientGroup.eq_one_iff x

theorem le_of_normalizes_of_coprime {G : Type*} [Group G] [Finite G]
    (Y Θ B : Subgroup G) (hYΘ : Y ≤ Subgroup.normalizer (Θ : Set G))
    (hΘ : ¬ 3 ∣ Nat.card Θ) (hB : IsPGroup 3 B)
    (hBY : B ≤ Subgroup.normalizer (Y : Set G)) (hBle : B ≤ Y ⊔ Θ) : B ≤ Y := by
  intro b hb
  have hbΘ : b ∈ (↑(Y ⊔ Θ) : Set G) := hBle hb
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Y Θ hYΘ] at hbΘ
  obtain ⟨y, hy, t, ht, hyt⟩ := hbΘ
  have hyN : y ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hy
  have hbN : b ∈ Subgroup.normalizer (Y : Set G) := hBY hb
  have htN : t ∈ Subgroup.normalizer (Y : Set G) := by
    have ht' : t = y⁻¹ * b := by rw [← hyt, inv_mul_cancel_left]
    rw [ht']
    exact mul_mem (inv_mem hyN) hbN
  let qmap := QuotientGroup.mk' (Y.subgroupOf (Subgroup.normalizer (Y : Set G)))
  have hπy : qmap ⟨y, hyN⟩ = 1 :=
    (aux_IndexArg_mk'_eq_one_iff (Y.subgroupOf (Subgroup.normalizer (Y : Set G)))
      (⟨y, hyN⟩ : Subgroup.normalizer (Y : Set G))).2 (Subgroup.mem_subgroupOf.2 hy)
  have hbt : qmap ⟨b, hbN⟩ = qmap ⟨t, htN⟩ := by
    have hsplit : (⟨b, hbN⟩ : Subgroup.normalizer (Y : Set G)) = ⟨y, hyN⟩ * ⟨t, htN⟩ :=
      Subtype.ext hyt.symm
    rw [hsplit, map_mul, hπy, one_mul]
  have hc : qmap ⟨t, htN⟩ ^ Nat.card Θ = 1 := by
    rw [← map_pow, aux_IndexArg_subtype_pow_eq_one (Subgroup.normalizer (Y : Set G)) ⟨t, htN⟩ _
      (orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard Θ ht)), map_one]
  obtain ⟨k, hk⟩ := hB ⟨b, hb⟩
  have hk' : b ^ 3 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hb3 : qmap ⟨b, hbN⟩ ^ 3 ^ k = 1 := by
    rw [← map_pow, aux_IndexArg_subtype_pow_eq_one (Subgroup.normalizer (Y : Set G)) ⟨b, hbN⟩ _ hk',
      map_one]
  have hcop : Nat.gcd (3 ^ k) (Nat.card Θ) = 1 :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hΘ)
  have hd1 : orderOf (qmap ⟨b, hbN⟩) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hb3
  have hd2 : orderOf (qmap ⟨b, hbN⟩) ∣ Nat.card Θ := by
    rw [hbt]
    exact orderOf_dvd_of_pow_eq_one hc
  have hd : orderOf (qmap ⟨b, hbN⟩) = 1 := by
    have h := Nat.dvd_gcd hd1 hd2
    rw [hcop] at h
    exact Nat.dvd_one.1 h
  have hb1 : qmap ⟨b, hbN⟩ = 1 := orderOf_eq_one_iff.1 hd
  exact Subgroup.mem_subgroupOf.1
    ((aux_IndexArg_mk'_eq_one_iff (Y.subgroupOf (Subgroup.normalizer (Y : Set G)))
      (⟨b, hbN⟩ : Subgroup.normalizer (Y : Set G))).1 hb1)

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
