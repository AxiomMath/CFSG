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

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem s16t3_exists_pow_three_part {A R : Subgroup G} {u₀ : G} {n : ℕ}
    (hu₀ : u₀ ∈ A) (hu₀R : u₀ ^ 3 ^ n ∈ R) (hR : IsPGroup 2 ↥R) (hn : n ≠ 0) :
    ∃ u ∈ A, u ^ 3 ^ n = 1 ∧ u * u₀⁻¹ ∈ R := by
  obtain ⟨s, hs⟩ := hR ⟨u₀ ^ 3 ^ n, hu₀R⟩
  have hs' : u₀ ^ (3 ^ n * 2 ^ s) = 1 := by
    have h := congrArg Subtype.val hs
    simpa [pow_mul] using h
  have hcop : Nat.Coprime (2 ^ s) (3 ^ n) :=
    Nat.Coprime.pow s n (by norm_num : Nat.Coprime 2 3)
  have hN1 : 1 < 3 ^ n := Nat.one_lt_pow hn (by norm_num)
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hN1
  refine ⟨u₀ ^ (2 ^ s * t), A.pow_mem hu₀ _, ?_, ?_⟩
  · rw [← pow_mul]
    rw [show (2 ^ s * t) * 3 ^ n = (3 ^ n * 2 ^ s) * t by ring]
    rw [pow_mul, hs', one_pow]
  · have hk_eq : 2 ^ s * t = 3 ^ n * (2 ^ s * t / 3 ^ n) + 1 := by
      have h := Nat.div_add_mod (2 ^ s * t) (3 ^ n)
      rw [ht] at h
      exact h.symm
    have hu_eq : u₀ ^ (2 ^ s * t) = (u₀ ^ 3 ^ n) ^ (2 ^ s * t / 3 ^ n) * u₀ := by
      nth_rewrite 1 [hk_eq]
      rw [pow_add, pow_mul, pow_one]
    rw [hu_eq, mul_assoc, mul_inv_cancel, mul_one]
    exact R.pow_mem hu₀R _

theorem s16t3_exists_three_parts {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hBA : B ≤ normalizer (A : Set G)) (hR : IsPGroup 2 ↥(A ⊓ B)) {y : G} (hy : y ∈ A ⊔ B)
    {n : ℕ} (hyn : y ^ 3 ^ n = 1) :
    ∃ u ∈ A, ∃ v ∈ B, u ^ 3 ^ n = 1 ∧ v ^ 3 ^ n = 1 ∧ y * (u * v)⁻¹ ∈ A ⊓ B := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨1, A.one_mem, 1, B.one_mem, by simp, by simp, ?_⟩
    have hy1 : y = 1 := by simpa using hyn
    rw [hy1]
    simp
  set S : Subgroup G := A ⊔ B with hS
  have hA_S : A ≤ S := by rw [hS]; exact le_sup_left
  have hB_S : B ≤ S := by rw [hS]; exact le_sup_right
  haveI hAn : (A.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA_S).mpr (by
      rw [hS]; exact sup_le Subgroup.le_normalizer hBA)
  haveI hBn : (B.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hB_S).mpr (by
      rw [hS]; exact sup_le hAB Subgroup.le_normalizer)
  have hR_S : A ⊓ B ≤ S := inf_le_left.trans hA_S
  have hnorm : S ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
    rw [hS]
    exact sup_le ((le_inf Subgroup.le_normalizer hAB).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := A) (K := B)))
      ((le_inf hBA Subgroup.le_normalizer).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := A) (K := B)))
  haveI hSnorm : ((A ⊓ B).subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hR_S).mpr hnorm
  have hyS : y ∈ S := by rw [hS]; exact hy
  have hyS' : (⟨y, hyS⟩ : ↥S) ∈ A.subgroupOf S ⊔ B.subgroupOf S := by
    rw [← Subgroup.subgroupOf_sup hA_S hB_S, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨u₀S, hu₀S, v₀S, hv₀S, hdec⟩ := (Subgroup.mem_sup_of_normal_right
    (s := A.subgroupOf S) (t := B.subgroupOf S)).1 hyS'
  have hu₀ : (u₀S : G) ∈ A := Subgroup.mem_subgroupOf.mp hu₀S
  have hv₀ : (v₀S : G) ∈ B := Subgroup.mem_subgroupOf.mp hv₀S
  let q : ↥S →* (↥S ⧸ (A ⊓ B).subgroupOf S) := QuotientGroup.mk' _
  have hcommAB : ⁅A, B⁆ ≤ A ⊓ B :=
    le_inf (by
        rw [Subgroup.commutator_comm]
        exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hBA)
      ((Subgroup.le_normalizer_iff_commutator_le_right).mp hAB)
  have hcoe : ((⁅u₀S, v₀S⁆ : ↥S) : G) = ⁅(u₀S : G), (v₀S : G)⁆ := by
    rw [show ((⁅u₀S, v₀S⁆ : ↥S) : G) = (Subgroup.subtype S) ⁅u₀S, v₀S⁆ from rfl]
    exact map_commutatorElement (Subgroup.subtype S) u₀S v₀S
  have hu₀v₀S : ⁅u₀S, v₀S⁆ ∈ (A ⊓ B).subgroupOf S := by
    rw [Subgroup.mem_subgroupOf, hcoe]
    exact hcommAB (Subgroup.commutator_mem_commutator hu₀ hv₀)
  have hcomm : Commute (q u₀S) (q v₀S) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅u₀S, v₀S⁆).mpr hu₀v₀S
  have hySpow : (⟨y, hyS⟩ : ↥S) ^ (3 ^ n) = 1 := by
    apply Subtype.ext
    simpa using hyn
  have hqy_pow : q (⟨y, hyS⟩ : ↥S) ^ (3 ^ n) = 1 := by
    rw [← map_pow, hySpow, map_one]
  have hqy_eq : q (⟨y, hyS⟩ : ↥S) = q u₀S * q v₀S := by
    rw [← hdec, map_mul]
  have hprod_q : q u₀S ^ (3 ^ n) * q v₀S ^ (3 ^ n) = 1 := by
    rw [← hcomm.mul_pow, ← hqy_eq]
    exact hqy_pow
  have hu₀v₀R : (u₀S : G) ^ (3 ^ n) * (v₀S : G) ^ (3 ^ n) ∈ A ⊓ B := by
    have hmem : u₀S ^ (3 ^ n) * v₀S ^ (3 ^ n) ∈ (A ⊓ B).subgroupOf S :=
      (QuotientGroup.eq_one_iff _).mp (by
        change q (u₀S ^ (3 ^ n) * v₀S ^ (3 ^ n)) = 1
        rw [map_mul, map_pow, map_pow, hprod_q])
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  have hpow_u : (u₀S : G) ^ (3 ^ n) ∈ A ⊓ B := by
    refine ⟨A.pow_mem hu₀ _, ?_⟩
    have heq : (u₀S : G) ^ (3 ^ n) =
        ((u₀S : G) ^ (3 ^ n) * (v₀S : G) ^ (3 ^ n)) * ((v₀S : G) ^ (3 ^ n))⁻¹ := by
      group
    rw [heq]
    exact B.mul_mem (Subgroup.mem_inf.mp hu₀v₀R).2 (B.inv_mem (B.pow_mem hv₀ _))
  have hpow_v : (v₀S : G) ^ (3 ^ n) ∈ A ⊓ B := by
    refine ⟨?_, B.pow_mem hv₀ _⟩
    have heq : (v₀S : G) ^ (3 ^ n) =
        ((u₀S : G) ^ (3 ^ n))⁻¹ * ((u₀S : G) ^ (3 ^ n) * (v₀S : G) ^ (3 ^ n)) := by
      group
    rw [heq]
    exact A.mul_mem (A.inv_mem (A.pow_mem hu₀ _)) (Subgroup.mem_inf.mp hu₀v₀R).1
  obtain ⟨u, huA, huN, huR⟩ := s16t3_exists_pow_three_part hu₀ hpow_u hR hn
  obtain ⟨v, hvB, hvN, hvR⟩ := s16t3_exists_pow_three_part hv₀ hpow_v hR hn
  refine ⟨u, huA, v, hvB, huN, hvN, ?_⟩
  have huS : u ∈ S := hA_S huA
  have hvS : v ∈ S := hB_S hvB
  let uS : ↥S := ⟨u, huS⟩
  let vS : ↥S := ⟨v, hvS⟩
  have huS_R : uS * u₀S⁻¹ ∈ (A ⊓ B).subgroupOf S := by
    rw [Subgroup.mem_subgroupOf]
    simpa [uS] using huR
  have hvS_R : vS * v₀S⁻¹ ∈ (A ⊓ B).subgroupOf S := by
    rw [Subgroup.mem_subgroupOf]
    simpa [vS] using hvR
  have hqu : q uS = q u₀S := by
    have h1 : q (uS * u₀S⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr huS_R
    have h2 : q uS * (q u₀S)⁻¹ = 1 := by simpa only [map_mul, map_inv] using h1
    exact mul_inv_eq_one.mp h2
  have hqv : q vS = q v₀S := by
    have h1 : q (vS * v₀S⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hvS_R
    have h2 : q vS * (q v₀S)⁻¹ = 1 := by simpa only [map_mul, map_inv] using h1
    exact mul_inv_eq_one.mp h2
  have hfinal_q : q (⟨y, hyS⟩ * (uS * vS)⁻¹) = 1 := by
    simp only [map_mul, map_inv, hqy_eq, hqu, hqv]
    exact mul_inv_cancel _
  have hmem : ⟨y, hyS⟩ * (uS * vS)⁻¹ ∈ (A ⊓ B).subgroupOf S :=
    (QuotientGroup.eq_one_iff _).mp (by
      change q (⟨y, hyS⟩ * (uS * vS)⁻¹) = 1
      exact hfinal_q)
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa [uS, vS] using hmem

theorem s16t3_cube_mem_inf_of_normalizing {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hBA : B ≤ normalizer (A : Set G)) {y u v : G} (hu : u ∈ A) (hv : v ∈ B)
    (hy : y * (u * v)⁻¹ ∈ A ⊓ B) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) : y ^ 3 ∈ A ⊓ B := by
  have hcommAB : ⁅A, B⁆ ≤ A ⊓ B :=
    le_inf (by
        rw [Subgroup.commutator_comm]
        exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hBA)
      ((Subgroup.le_normalizer_iff_commutator_le_right).mp hAB)
  have huv : ⁅u, v⁆ ∈ A ⊓ B := hcommAB (Subgroup.commutator_mem_commutator hu hv)
  set S : Subgroup G := A ⊔ B with hS
  have hA_S : A ≤ S := by rw [hS]; exact le_sup_left
  have hB_S : B ≤ S := by rw [hS]; exact le_sup_right
  have hR_S : A ⊓ B ≤ S := inf_le_left.trans hA_S
  have hnorm : S ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
    rw [hS]
    exact sup_le ((le_inf Subgroup.le_normalizer hAB).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := A) (K := B)))
      ((le_inf hBA Subgroup.le_normalizer).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := A) (K := B)))
  haveI hSnorm : ((A ⊓ B).subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hR_S).mpr hnorm
  have hyS : y ∈ S := by
    have huvS : u * v ∈ S := S.mul_mem (hA_S hu) (hB_S hv)
    have h1 : y * (u * v)⁻¹ ∈ S := hR_S hy
    have hy_eq : y = (y * (u * v)⁻¹) * (u * v) := by group
    rw [hy_eq]
    exact S.mul_mem h1 huvS
  let uS : ↥S := ⟨u, hA_S hu⟩
  let vS : ↥S := ⟨v, hB_S hv⟩
  let yS : ↥S := ⟨y, hyS⟩
  let q : ↥S →* (↥S ⧸ (A ⊓ B).subgroupOf S) := QuotientGroup.mk' _
  have hq : q yS = q uS * q vS := by
    have h2 : q (yS * (uS * vS)⁻¹) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [Subgroup.mem_subgroupOf]
      simpa [yS, uS, vS] using hy
    have h3 : q yS * (q uS * q vS)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using h2
    exact mul_inv_eq_one.mp h3
  have hcoe : ((⁅uS, vS⁆ : ↥S) : G) = ⁅(uS : G), (vS : G)⁆ := by
    rw [show ((⁅uS, vS⁆ : ↥S) : G) = (Subgroup.subtype S) ⁅uS, vS⁆ from rfl]
    exact map_commutatorElement (Subgroup.subtype S) uS vS
  have hu_vS : ⁅uS, vS⁆ ∈ (A ⊓ B).subgroupOf S := by
    rw [Subgroup.mem_subgroupOf, hcoe]
    exact huv
  have hcomm : Commute (q uS) (q vS) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅uS, vS⁆).mpr hu_vS
  have huS3 : uS ^ 3 = 1 := by apply Subtype.ext; simpa using hu3
  have hvS3 : vS ^ 3 = 1 := by apply Subtype.ext; simpa using hv3
  have hy3 : yS ^ 3 ∈ (A ⊓ B).subgroupOf S :=
    (QuotientGroup.eq_one_iff (yS ^ 3)).mp (by
      change q (yS ^ 3) = 1
      rw [map_pow, hq, hcomm.mul_pow, ← map_pow, ← map_pow, huS3, hvS3, map_one, mul_one])
  rw [Subgroup.mem_subgroupOf] at hy3
  simpa [yS] using hy3

theorem s16t3_le_of_isPGroup_three {N T Y : Subgroup G} (hTN : T ≤ normalizer (N : Set G))
    (hT : IsPGroup 2 ↥T) (hY : IsPGroup 3 ↥Y) (hYS : Y ≤ N ⊔ T) : Y ≤ N := by
  intro y hyY
  haveI hNS : (N.subgroupOf (N ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTN)
  have hyS : y ∈ N ⊔ T := hYS hyY
  have hyS' : (⟨y, hyS⟩ : ↥(N ⊔ T)) ∈
      N.subgroupOf (N ⊔ T) ⊔ T.subgroupOf (N ⊔ T) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, t, ht, hnt⟩ := (Subgroup.mem_sup_of_normal_left
    (s := N.subgroupOf (N ⊔ T)) (t := T.subgroupOf (N ⊔ T))).1 hyS'
  have hnN : (n : G) ∈ N := (Subgroup.mem_subgroupOf.mp hn)
  have htT : (t : G) ∈ T := (Subgroup.mem_subgroupOf.mp ht)
  obtain ⟨k, hk⟩ := hY ⟨y, hyY⟩
  have hk' : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨l, hl⟩ := hT ⟨(t : G), htT⟩
  have hl' : (t : G) ^ 2 ^ l = 1 := by simpa using congrArg Subtype.val hl
  have hval : (n : G) * (t : G) = y := by
    have := congrArg Subtype.val hnt
    simpa using this
  have hn1 : QuotientGroup.mk' (N.subgroupOf (N ⊔ T)) n = 1 :=
    (QuotientGroup.eq_one_iff n).mpr hn
  have hx_eq : QuotientGroup.mk' (N.subgroupOf (N ⊔ T)) t =
      QuotientGroup.mk' (N.subgroupOf (N ⊔ T)) ⟨y, hyS⟩ := by
    rw [← hnt, map_mul, hn1, one_mul]
  have hySpow : (⟨y, hyS⟩ : ↥(N ⊔ T)) ^ 3 ^ k = 1 := by
    apply Subtype.ext
    simpa using hk'
  have htpow : t ^ 2 ^ l = 1 := by
    apply Subtype.ext
    simpa using hl'
  have hx3 : (QuotientGroup.mk' (N.subgroupOf (N ⊔ T)) t) ^ 3 ^ k = 1 := by
    rw [hx_eq, ← map_pow, hySpow, map_one]
  have hx2 : (QuotientGroup.mk' (N.subgroupOf (N ⊔ T)) t) ^ 2 ^ l = 1 := by
    rw [← map_pow, htpow, map_one]
  have hord3 : orderOf (QuotientGroup.mk' (N.subgroupOf (N ⊔ T)) t) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one hx3
  have hord2 : orderOf (QuotientGroup.mk' (N.subgroupOf (N ⊔ T)) t) ∣ 2 ^ l :=
    orderOf_dvd_of_pow_eq_one hx2
  have hone : orderOf (QuotientGroup.mk' (N.subgroupOf (N ⊔ T)) t) = 1 := by
    have hdiv : orderOf (QuotientGroup.mk' (N.subgroupOf (N ⊔ T)) t) ∣ 1 := by
      rw [← (Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 3 2)).gcd_eq_one]
      exact Nat.dvd_gcd hord3 hord2
    exact Nat.dvd_one.mp hdiv
  have hx1 : QuotientGroup.mk' (N.subgroupOf (N ⊔ T)) t = 1 := orderOf_eq_one_iff.mp hone
  have htN : (t : G) ∈ N := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff t).mp hx1)
  rw [← hval]
  exact N.mul_mem hnN htN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
