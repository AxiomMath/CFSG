module


import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2Grp
import CFSG.LargeExtraspecial.S3Fourteen
import CFSG.RankThree.Literature.FSmithForm
import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
import CFSG.RankThree.PartTwo.Sec8.Hering88NLinAlg
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

namespace Q16Grp

open Subgroup
open scoped commutatorElement
open CFSG.RankThree.Literature.FSmith (conjEndo conjEndo_apply exists_ofMul_of
  extraspecialConjOrth_apply mem_of_extraspecialConjOrth_eq_one ofMul_of_eq_zero_iff ofMul_of_mul
  sq_mem_center)

private theorem exists_orderOf_mul_two_eq_card {R : Type*} [Group R] [Finite R] (hR : IsPGroup 2 R)
    {z : R} (hzz : z * z = 1) (hz1 : z ≠ 1) (hC : Nat.card (centralizer ({z} : Set R)) ≤ 4)
    (h8 : 8 ≤ Nat.card R) : ∃ a : R, orderOf a * 2 = Nat.card R := by
  haveI : Finite (Shrink.{0} R) := Finite.of_equiv R (equivShrink.{0} R)
  let e : Shrink.{0} R ≃* R := Shrink.mulEquiv
  have hcard : Nat.card (Shrink.{0} R) = Nat.card R := Nat.card_congr e.toEquiv
  have hC' : Nat.card (centralizer ({e.symm z} : Set (Shrink.{0} R))) ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : centralizer ({e.symm z} : Set (Shrink.{0} R)) =>
        (⟨e x, ?_⟩ : centralizer ({z} : Set R))) ?_) hC
    · have hx := mem_centralizer_iff.1 x.2 (e.symm z) rfl
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have := congrArg e hx
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    · intro x y hxy
      exact Subtype.ext (e.injective (congrArg Subtype.val hxy))
  obtain ⟨a, ha, -⟩ := CFSG.GH74.GLS.Stage1.Thm6.Sec13.exists_cyclic_index_two
    (Nat.card (Shrink.{0} R)) (Shrink.{0} R) rfl (hR.of_equiv e.symm) (e.symm z)
    (by rw [← map_mul, hzz, map_one]) (fun h => hz1 (by simpa using h)) hC' (hcard ▸ h8)
  exact ⟨e a, by rw [MulEquiv.orderOf_eq, ha, hcard]⟩

private theorem card_le_eight_mul_of_exponent {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H)
    {N S : Subgroup H} [N.Normal] (hS : Nat.card S ≤ 4 * Nat.card N) {a : H} (haN : a ∉ N)
    (ha2 : a * a ∈ N) (hcent : ∀ h : H, ⁅h, a⁆ ∈ N → h ∈ S) (hexp : ∀ h : H, h ^ 4 ∈ N) :
    Nat.card H ≤ 8 * Nat.card N := by
  have hNpos : 0 < Nat.card N := Nat.card_pos
  set r : H ⧸ N := QuotientGroup.mk a with hr
  have hrr : r * r = 1 := by
    rw [hr, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).2 ha2
  have hr1 : r ≠ 1 := fun h => haN ((QuotientGroup.eq_one_iff a).1 h)
  have hC : Nat.card (centralizer ({r} : Set (H ⧸ N))) ≤ 4 := by
    have h1 := QuotientGroup.card_preimage_mk N (centralizer ({r} : Set (H ⧸ N)) : Set (H ⧸ N))
    have h2 : Nat.card (QuotientGroup.mk ⁻¹' (centralizer ({r} : Set (H ⧸ N)) : Set (H ⧸ N))) ≤
        Nat.card S := by
      refine Nat.card_mono (Set.toFinite _) fun h hh => hcent h ?_
      have hc := mem_centralizer_iff.1 hh r rfl
      refine (QuotientGroup.eq_one_iff _).1 ?_
      change (QuotientGroup.mk' N) ⁅h, a⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 hc.symm
    rw [h1] at h2
    exact Nat.le_of_mul_le_mul_left (by linarith) hNpos
  have hR8 : Nat.card (H ⧸ N) ≤ 8 := by
    by_contra hlt
    obtain ⟨b, hb⟩ := exists_orderOf_mul_two_eq_card (hH.to_quotient N) hrr hr1 hC
      (by omega)
    have hb4 : b ^ 4 = 1 := by
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).2 (hexp h)
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hb4)
    omega
  calc Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup N
    _ ≤ 8 * Nat.card N := Nat.mul_le_mul_right _ hR8

private theorem pow_four_eq_one_of_pow_two_pow {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (hrank : Module.finrank (ZMod 2) V ≤ 4)
    (L : Module.End (ZMod 2) V) (hL : ∃ k : ℕ, L ^ 2 ^ k = 1) : L ^ 4 = 1 := by
  obtain ⟨k, hk⟩ := hL
  let φ := LinearMap.toMatrixAlgEquiv (Module.finBasis (ZMod 2) V)
  have h1 : (φ L) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have h2 := CFSG.RankThree.PartTwo.Sec8.Hering88N.pow_four_eq_one_of_two_power_le_four hrank
    ⟨k, h1⟩
  apply φ.injective
  rw [map_pow, h2, map_one]

private theorem two_nsmul_eq_zero_of_extraspecial {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsExtraspecialPGroup 2 Q) (v : Additive (Abelianization Q)) : 2 • v = 0 := by
  obtain ⟨x, rfl⟩ := exists_ofMul_of v
  rw [two_nsmul, ← ofMul_of_mul, ofMul_of_eq_zero_iff hQ, ← pow_two]
  exact sq_mem_center hQ x

private theorem pow_four_mem_of_extraspecial {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H)
    {Q : Subgroup H} (hQn : Q.Normal) (hQ : IsExtraspecialPGroup 2 Q) (hcard : Nat.card Q = 32)
    (hCQ : centralizer (Q : Set H) ≤ Q) (g : H) : g ^ 4 ∈ Q := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    AddCommGroup.zmodModule (two_nsmul_eq_zero_of_extraspecial hQ)
  have hfin : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  have hcardV : Nat.card (Additive (Abelianization Q)) = 16 := by
    have h1 : Nat.card Q = Nat.card (Abelianization Q) * Nat.card (commutator Q) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator Q)
    rw [hQ.2.1, hQ.2.2.2, hcard] at h1
    rw [Nat.card_congr Additive.toMul]
    omega
  have hrank : Module.finrank (ZMod 2) (Additive (Abelianization Q)) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (Abelianization Q))
    rw [hcardV, Nat.card_zmod] at h
    exact Nat.pow_right_injective (le_refl 2) (by omega : 2 ^ _ = 2 ^ 4)
  have hL4 : (conjEndo hQn g) ^ 4 = 1 := by
    obtain ⟨k, hk⟩ := hH g
    exact pow_four_eq_one_of_pow_two_pow hrank.le (conjEndo hQn g)
      ⟨k, by rw [← map_pow, hk, map_one]⟩
  refine mem_of_extraspecialConjOrth_eq_one hQ hQn hCQ (g := g ^ 4) ?_
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨x, rfl⟩ := exists_ofMul_of v
  have h1 := LinearMap.congr_fun (by rw [map_pow, hL4] : conjEndo hQn (g ^ 4) = 1)
    (Additive.ofMul (Abelianization.of x))
  rw [conjEndo_apply, Module.End.one_apply] at h1
  rw [extraspecialConjOrth_apply, h1]
  rfl

variable {G : Type*} [Group G] [Finite G]

theorem pow_four_mem {T O : Subgroup G} (hOT : O ≤ T) (hT : IsPGroup 2 T)
    (hOn : ∀ t ∈ T, ∀ x ∈ O, t * x * t⁻¹ ∈ O) {z : G} (hzO : z ∈ O) (hz1 : z ≠ 1)
    (hz2 : z * z = 1) (hzT : ∀ t ∈ T, t * z = z * t)
    (hZ : ∀ x ∈ O, (∀ y ∈ O, x * y = y * x) → x = 1 ∨ x = z)
    (hcomm : ∀ x ∈ O, ∀ y ∈ O, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z)
    (hcard : Nat.card O = 32) (hC : ∀ t ∈ T, (∀ x ∈ O, t * x = x * t) → t ∈ O) :
    ∀ t ∈ T, t ^ 4 ∈ O := by
  have hzc : ∀ y ∈ O, y * z = z * y := fun y hy => hzT y (hOT hy)
  have hcenter : ∀ x : O, x ∈ center O ↔ (x : G) = 1 ∨ (x : G) = z := by
    intro x
    rw [mem_center_iff]
    constructor
    · intro hx
      refine hZ x x.2 fun y hy => ?_
      exact congrArg Subtype.val (hx ⟨y, hy⟩).symm
    · intro hx y
      rcases hx with hx | hx
      · apply Subtype.ext
        simp [hx]
      · apply Subtype.ext
        simpa [hx] using hzc y y.2
  have hz' : (⟨z, hzO⟩ : O) ∈ center O := (hcenter _).2 (Or.inr rfl)
  have hzord : orderOf (⟨z, hzO⟩ : O) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa [pow_two] using hz2))
      (fun h => hz1 (congrArg Subtype.val h))
  have hcenterEq : center O = zpowers (⟨z, hzO⟩ : O) := by
    refine le_antisymm (fun x hx => ?_) (zpowers_le.2 hz')
    rcases (hcenter x).1 hx with h | h
    · have : x = 1 := Subtype.ext h
      rw [this]
      exact one_mem _
    · have : x = ⟨z, hzO⟩ := Subtype.ext h
      rw [this]
      exact mem_zpowers _
  have hcenterCard : Nat.card (center O) = 2 := by
    rw [hcenterEq, Nat.card_zpowers, hzord]
  have hOext : IsExtraspecialPGroup 2 O := by
    refine CFSG.LargeExtraspecial.isExtraspecialPGroup_of_card_center (hT.to_le hOT) hcenterCard
      (fun x y => (hcenter _).2 ?_) (fun x => (hcenter _).2 ?_) ?_
    · have h := hcomm x x.2 y y.2
      simpa [commutatorElement_def] using h
    · refine hZ _ (O.pow_mem x.2 2) fun y hy => ?_
      have hc := hcomm x x.2 y hy
      have hxy : (x : G) * y = z * y * x ∨ (x : G) * y = y * x := by
        rcases hc with hc | hc
        · right
          have := congrArg (· * ((y : G) * x)) hc
          simpa [mul_assoc] using this
        · left
          have := congrArg (· * ((y : G) * x)) hc
          simpa [mul_assoc] using this
      have hxz : (x : G) * z = z * x := hzc x x.2
      rcases hxy with h | h
      · calc (x : G) ^ 2 * y = x * (x * y) := by rw [pow_two, mul_assoc]
          _ = x * (z * y * x) := by rw [h]
          _ = (x * z) * y * x := by simp only [mul_assoc]
          _ = z * x * y * x := by rw [hxz]
          _ = z * (x * y) * x := by simp only [mul_assoc]
          _ = z * (z * y * x) * x := by rw [h]
          _ = (z * z) * y * (x * x) := by simp only [mul_assoc]
          _ = y * x ^ 2 := by rw [hz2, one_mul, pow_two]
      · calc (x : G) ^ 2 * y = x * (x * y) := by rw [pow_two, mul_assoc]
          _ = x * (y * x) := by rw [h]
          _ = (x * y) * x := by rw [mul_assoc]
          _ = y * x * x := by rw [h]
          _ = y * x ^ 2 := by rw [pow_two, mul_assoc]
    · by_contra hnc
      push Not at hnc
      have htop : center O = ⊤ := eq_top_iff.2 fun x _ => mem_center_iff.2 fun y => hnc y x
      rw [htop, Subgroup.card_top, hcard] at hcenterCard
      omega
  haveI hQn : (O.subgroupOf T).Normal :=
    (normal_subgroupOf_iff hOT).2 fun n m hn hm => hOn m hm n hn
  have hQext : IsExtraspecialPGroup 2 (O.subgroupOf T) :=
    CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (subgroupOfEquivOfLe hOT).symm hOext
  have hQcard : Nat.card (O.subgroupOf T) = 32 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hOT).toEquiv]
    exact hcard
  have hCQ : centralizer ((O.subgroupOf T : Subgroup T) : Set T) ≤ O.subgroupOf T := by
    intro g hg
    rw [mem_subgroupOf]
    refine hC g g.2 fun x hx => ?_
    have := mem_centralizer_iff.1 hg ⟨x, hOT hx⟩ (mem_subgroupOf.2 hx)
    exact (congrArg Subtype.val this).symm
  intro t ht
  exact mem_subgroupOf.1 (pow_four_mem_of_extraspecial hT hQn hQext hQcard hCQ ⟨t, ht⟩)

theorem card_le_of_pow_four_mem {T O S : Subgroup G} (hOS : O ≤ S) (hST : S ≤ T)
    (hT : IsPGroup 2 T) (hOn : ∀ t ∈ T, ∀ x ∈ O, t * x * t⁻¹ ∈ O)
    (hS : Nat.card S ≤ 4 * Nat.card O) {q : G} (hqT : q ∈ T) (hqO : q ∉ O) (hq2 : q * q ∈ O)
    (hcent : ∀ t ∈ T, t * q * t⁻¹ * q⁻¹ ∈ O → t ∈ S) (hexp : ∀ t ∈ T, t ^ 4 ∈ O) :
    Nat.card T ≤ 8 * Nat.card O := by
  have hOT : O ≤ T := hOS.trans hST
  haveI : (O.subgroupOf T).Normal :=
    (normal_subgroupOf_iff hOT).2 fun n m hn hm => hOn m hm n hn
  have hOcard : Nat.card (O.subgroupOf T) = Nat.card O :=
    Nat.card_congr (subgroupOfEquivOfLe hOT).toEquiv
  have hScard : Nat.card (S.subgroupOf T) = Nat.card S :=
    Nat.card_congr (subgroupOfEquivOfLe hST).toEquiv
  have h := card_le_eight_mul_of_exponent (H := T) hT (N := O.subgroupOf T) (S := S.subgroupOf T)
    (by rw [hOcard, hScard]; exact hS) (a := ⟨q, hqT⟩) (fun h => hqO (mem_subgroupOf.1 h))
    (mem_subgroupOf.2 hq2)
    (fun h hh => mem_subgroupOf.2 (hcent h h.2 (by
      have := mem_subgroupOf.1 hh
      simpa [commutatorElement_def] using this)))
    (fun h => mem_subgroupOf.2 (hexp h h.2 |> fun h' => by simpa using h'))
  rwa [hOcard] at h

end Q16Grp

end CFSG.RankThree.PartTwo.Sec19.SolEven
