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

namespace CFSG.Quasithin.H13.NFa2

open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_of_odd_orderOf_of_le_sup {L T : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {y : G} (hy : y ∈ L ⊔ T)
    (hodd : Odd (orderOf y)) : y ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hset : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T hTL
  have hy' : y ∈ (L : Set G) * (T : Set G) := by rw [← hset]; exact hy
  obtain ⟨l, hl, t, ht, rfl⟩ := hy'
  let N : Subgroup ↥(L ⊔ T) := L.subgroupOf (L ⊔ T)
  have hN : N.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le hLN hTL
  let φ : ↥(L ⊔ T) →* ↥(L ⊔ T) ⧸ N := QuotientGroup.mk' N
  let tt : ↥(L ⊔ T) := ⟨t, Subgroup.mem_sup_right ht⟩
  let ll : ↥(L ⊔ T) := ⟨l, Subgroup.mem_sup_left hl⟩
  have hlN : ll ∈ N := by
    show ll ∈ L.subgroupOf (L ⊔ T)
    exact hl
  have hφl : φ ll = 1 := (QuotientGroup.eq_one_iff ll).mpr hlN
  have hφ : φ (ll * tt) = φ tt := by
    rw [map_mul, hφl, one_mul]
  have h1 : orderOf (φ (ll * tt)) ∣ orderOf (l * t) := by
    have := orderOf_map_dvd φ (ll * tt)
    rw [Subgroup.orderOf_mk (G := G) (H := L ⊔ T)] at this
    simpa using this
  have h2 : orderOf (φ tt) ∣ orderOf t := by
    have := orderOf_map_dvd φ tt
    have e : orderOf tt = orderOf t := Subgroup.orderOf_mk t _
    rwa [e] at this
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨t, ht⟩
  rw [Subgroup.orderOf_mk] at hk
  have h3 : orderOf (φ (ll * tt)) = 1 := by
    rw [hφ] at h1 ⊢
    have h4 : orderOf (φ tt) ∣ 2 ^ k := hk ▸ h2
    have h5 : Odd (orderOf (φ tt)) := Odd.of_dvd_nat hodd h1
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
    rcases j with _ | j
    · simpa using hj'
    · exfalso
      rw [hj'] at h5
      exact (Nat.not_even_iff_odd.mpr h5) (by simp [pow_succ, Nat.even_mul])
  have h6 : φ (ll * tt) = 1 := orderOf_eq_one_iff.mp h3
  have h7 : ll * tt ∈ N := (QuotientGroup.eq_one_iff _).mp h6
  have h8 : l * t ∈ L := h7
  exact h8

theorem isPGroup_two_of_le_sup [Finite G] {L T C : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hC : C ≤ L ⊔ T)
    (hCL : IsPGroup 2 ↥(C ⊓ L)) : IsPGroup 2 ↥C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.iff_orderOf.mpr fun x => ?_
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : G)).ne'
  have hxo : orderOf (x : G) = orderOf x := Subgroup.orderOf_coe x
  set y : G := (x : G) ^ (2 ^ a) with hy
  have hdvd : 2 ^ a ∣ orderOf (x : G) := by rw [hab]; exact dvd_mul_right _ _
  have hyo : orderOf y = b := by
    rw [hy, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) hdvd, hab]
    exact Nat.mul_div_cancel_left b (by positivity)
  have hyC : y ∈ C := C.pow_mem x.2 _
  have hyL : y ∈ L := mem_of_odd_orderOf_of_le_sup hT hTL (hC hyC) (hyo ▸ hb)
  obtain ⟨c, hc⟩ := (IsPGroup.iff_orderOf.mp hCL) ⟨y, Subgroup.mem_inf.mpr ⟨hyC, hyL⟩⟩
  rw [Subgroup.orderOf_mk, hyo] at hc
  have hb1 : b = 1 := by
    rcases c with _ | c
    · simpa using hc
    · exfalso
      have : Odd (2 ^ (c + 1)) := hc ▸ hb
      exact (Nat.not_even_iff_odd.mpr this) (by simp [pow_succ, Nat.even_mul])
  exact ⟨a, by rw [← hxo, hab, hb1, mul_one]⟩

end CFSG.Quasithin.H13.NFa2
