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
public import Mathlib.GroupTheory.NoncommCoprod
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

namespace CFSG.RankThree.PartOne.SPOR

open Subgroup

theorem no_sylow_five_centre {T : Type*} [Group T] [Finite T] {m : ℕ}
    (hT : Nat.card T = 5 ^ 4 * m) (hm : ¬ 5 ∣ m) {P : Subgroup T} (hP : Nat.card P = 5 ^ 4)
    {x : T} (hx : x ^ 5 = 1) (hZ : ∀ z ∈ P, (∀ y ∈ P, z * y = y * z) → z ∈ zpowers x) {b : T}
    (hb : orderOf b = 5) {K : Subgroup T} (hKb : ∀ k ∈ K, b * k = k * b)
    (hK : 5 ^ 3 ∣ Nat.card K) (hKc : ∀ k ∈ K, (∀ l ∈ K, k * l = l * k) → k = 1) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hbK : b ∉ K := fun hbK => by
    have h1 : b = 1 := hKc b hbK (fun l hl => hKb l hl)
    rw [h1, orderOf_one] at hb
    exact absurd hb (by norm_num)
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := K) 5 (n := 3) hK
  set Q : Subgroup T := S.map K.subtype with hQ
  have hQcard : Nat.card Q = 5 ^ 3 := by
    rw [hQ, Subgroup.card_map_of_injective K.subtype_injective, hS]
  have hQK : ∀ q ∈ Q, q ∈ K := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hQp : IsPGroup 5 Q := IsPGroup.of_card hQcard
  have hQnt : Nontrivial Q := by
    rw [← Finite.one_lt_card_iff_nontrivial, hQcard]
    norm_num
  have hZnt : Nontrivial (center Q) := hQp.center_nontrivial
  have hcZ : IsPGroup 5 (center Q) := hQp.to_subgroup _
  have hdvd : 5 ∣ Nat.card (center Q) := by
    rcases hcZ.card_eq_or_dvd with h | h
    · have := Finite.one_lt_card_iff_nontrivial.2 hZnt
      omega
    · exact h
  obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' (G := center Q) 5 hdvd
  set z : T := (((z0 : Q) : T)) with hz
  have hzord : orderOf z = 5 := by
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz0]
  have hzQ : z ∈ Q := (z0 : Q).2
  have hzc : ∀ q ∈ Q, z * q = q * z := by
    intro q hq
    have := Subgroup.mem_center_iff.1 z0.2 ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  have hcomm : ∀ (q : Q) (c : zpowers b), Commute (Q.subtype q) ((zpowers b).subtype c) := by
    intro q c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 c.2
    show Commute (q : T) (c : T)
    rw [← hk]
    exact (show Commute b (q : T) from hKb q (hQK q q.2)).symm.zpow_right k
  let φ : Q × zpowers b →* T := MonoidHom.noncommCoprod Q.subtype (zpowers b).subtype hcomm
  have hφ : ∀ p : Q × zpowers b, φ p = (p.1 : T) * (p.2 : T) := fun p =>
    MonoidHom.noncommCoprod_apply _ _ _ _
  have hint : ∀ c ∈ zpowers b, c ∈ K → c = 1 := by
    have : Fact (Nat.card (zpowers b)).Prime := ⟨by rw [Nat.card_zpowers, hb]; norm_num⟩
    rcases (K.subgroupOf (zpowers b)).eq_bot_or_eq_top_of_prime_card with h | h
    · intro c hc hcK
      have h1 : (⟨c, hc⟩ : zpowers b) ∈ K.subgroupOf (zpowers b) := hcK
      rw [h, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    · exfalso
      apply hbK
      have h1 : (⟨b, mem_zpowers b⟩ : zpowers b) ∈ K.subgroupOf (zpowers b) := by
        rw [h]
        trivial
      exact h1
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨q, c⟩ h
    rw [hφ] at h
    have hqc : (q : T) = ((c : T))⁻¹ := eq_inv_of_mul_eq_one_left h
    have hcq : ((c : T))⁻¹ ∈ K := hqc ▸ hQK q q.2
    have hc1 : ((c : T))⁻¹ = 1 := hint _ (Subgroup.inv_mem _ c.2) hcq
    have hc : (c : T) = 1 := inv_eq_one.1 hc1
    have hq : (q : T) = 1 := by rw [hqc, hc1]
    exact Prod.ext (Subtype.ext hq) (Subtype.ext hc)
  set R := φ.range with hR
  have hRcard : Nat.card R = 5 ^ 4 := by
    rw [hR, Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm, Nat.card_prod, hQcard,
      Nat.card_zpowers, hb]
    norm_num
  have hfac : (Nat.card T).factorization 5 = 4 := by
    have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero 5)
    rw [hT, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm]
  let SP : Sylow 5 T := Sylow.ofCard P (by rw [hP, hfac])
  let SR : Sylow 5 T := Sylow.ofCard R (by rw [hRcard, hfac])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T SP SR
  have hmem : ∀ y : T, y ∈ ((g • SP : Sylow 5 T) : Set T) ↔ ∃ p ∈ P, g * p * g⁻¹ = y := by
    intro y
    rw [Sylow.coe_smul, Set.mem_smul_set]
    simp only [MulAut.smul_def, MulAut.conj_apply]
    exact Iff.rfl
  have hconj : ∀ r ∈ R, ∃ p ∈ P, g * p * g⁻¹ = r := by
    intro r hr
    apply (hmem r).1
    rw [hg]
    exact hr
  have hconj' : ∀ y ∈ P, g * y * g⁻¹ ∈ R := by
    intro y hy
    have h1 : g * y * g⁻¹ ∈ ((g • SP : Sylow 5 T) : Set T) := (hmem _).2 ⟨y, hy, rfl⟩
    rw [hg] at h1
    exact h1
  have hRelt : ∀ r ∈ R, ∃ q ∈ Q, ∃ c ∈ zpowers b, r = q * c := by
    rintro _ ⟨⟨q, c⟩, rfl⟩
    exact ⟨q, q.2, c, c.2, hφ _⟩
  have hzR : z ∈ R := ⟨(⟨z, hzQ⟩, 1), by rw [hφ]; simp⟩
  have hbR : b ∈ R := ⟨(1, ⟨b, mem_zpowers b⟩), by rw [hφ]; simp⟩
  have hzcen : ∀ r ∈ R, z * r = r * z := by
    intro r hr
    obtain ⟨q, hq, c, hc, rfl⟩ := hRelt r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    have h1 : z * q = q * z := hzc q hq
    have h2 : z * b ^ k = b ^ k * z :=
      (show Commute b z from hKb z (hQK z hzQ)).symm.zpow_right k
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  have hbcen : ∀ r ∈ R, b * r = r * b := by
    intro r hr
    obtain ⟨q, hq, c, hc, rfl⟩ := hRelt r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    have h1 : b * q = q * b := hKb q (hQK q hq)
    have h2 : b * b ^ k = b ^ k * b := (Commute.self_zpow b k)
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  have hZR : ∀ w ∈ R, (∀ y ∈ R, w * y = y * w) → w ∈ zpowers (g * x * g⁻¹) := by
    intro w hw hwc
    obtain ⟨p, hp, rfl⟩ := hconj w hw
    have hpc : ∀ y ∈ P, p * y = y * p := by
      intro y hy
      have h1 := hwc _ (hconj' y hy)
      have h2 : g * (p * y) * g⁻¹ = g * (y * p) * g⁻¹ := by
        simpa only [mul_assoc, inv_mul_cancel_left] using h1
      have h3 := mul_right_cancel h2
      exact mul_left_cancel h3
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hZ p hp hpc)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [conj_zpow, hk]⟩
  have hbx := hZR b hbR hbcen
  have hzx := hZR z hzR hzcen
  have hx5 : (g * x * g⁻¹) ^ 5 = 1 := by rw [conj_pow, hx]; simp
  have hle5 : orderOf (g * x * g⁻¹) ≤ 5 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx5)
  have hb_eq : zpowers b = zpowers (g * x * g⁻¹) := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hbx)
    rw [Nat.card_zpowers, Nat.card_zpowers, hb]
    exact hle5
  have hz_eq : zpowers z = zpowers (g * x * g⁻¹) := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzx)
    rw [Nat.card_zpowers, Nat.card_zpowers, hzord]
    exact hle5
  have hbz : b ∈ zpowers z := by
    rw [hz_eq, ← hb_eq]
    exact mem_zpowers b
  exact hbK (hQK b ((Subgroup.zpowers_le.2 hzQ) hbz))

end CFSG.RankThree.PartOne.SPOR
