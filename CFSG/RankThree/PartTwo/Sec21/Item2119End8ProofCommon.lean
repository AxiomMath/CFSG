module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofJ
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQ
import CFSG.RankThree.PartTwo.Sec21.Item2119End7ProofFinal
import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

namespace Item2119End8Proof

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_card {Q R : Subgroup G} (hQR : Q ≤ R) (hR3 : IsPGroup 3 R)
    (hcard : Nat.card R = 3 * Nat.card Q) : R ≤ Subgroup.normalizer (Q : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx : (Q.subgroupOf R).index = 3 := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := R)
    rw [inf_eq_left.mpr hQR, hcard] at h
    have hpos : 0 < Nat.card Q := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hR3
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hpos : 0 < Nat.card Q := Nat.card_pos
    rw [pow_zero] at hn
    omega
  have hmin : (Nat.card R).minFac = 3 := by
    rw [hn]
    exact Nat.Prime.pow_minFac Nat.prime_three hn0
  have hnorm : (Q.subgroupOf R).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hmin])
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQR).mp hnorm

omit [Finite G] in
theorem comm_of_relations {Q : Subgroup G} {d : G} (hd3 : d ^ 3 = 1)
    (hzc : ∀ z ∈ Subgroup.zpowers d, ∀ q ∈ Q, q * z = z * q)
    (hcommQ : ∀ y ∈ Q, ∀ q ∈ Q, y⁻¹ * (q * y * q⁻¹) ∈ Subgroup.zpowers d)
    {b₁ b₂ x p r : G} (hb₁ : b₁ ∈ Q) (hb₂ : b₂ ∈ Q) (hpQ : p ∈ Q) (hrQ : r ∈ Q)
    (hpdef : p = b₁ * x * b₁⁻¹ * x⁻¹) (hrdef : r = b₂ * x * b₂⁻¹ * x⁻¹)
    (hb : b₁ * b₂ = b₂ * b₁) (hpr : p * r = r * p) (h₁ : b₁ * p = p * b₁)
    (h₂ : b₂ * r = r * b₂)
    (h₁₂ : (b₁ * b₂) * ((b₁ * b₂) * x * (b₁ * b₂)⁻¹ * x⁻¹) =
      ((b₁ * b₂) * x * (b₁ * b₂)⁻¹ * x⁻¹) * (b₁ * b₂)) :
    b₁ * r = r * b₁ := by
  set z₁ := r⁻¹ * (b₁ * r * b₁⁻¹) with hz₁def
  set z₂ := p⁻¹ * (b₂ * p * b₂⁻¹) with hz₂def
  have hz₁ : z₁ ∈ Subgroup.zpowers d := hcommQ r hrQ b₁ hb₁
  have hz₂ : z₂ ∈ Subgroup.zpowers d := hcommQ p hpQ b₂ hb₂
  have hz₁c : ∀ q ∈ Q, q * z₁ = z₁ * q := hzc z₁ hz₁
  have hz₂c : ∀ q ∈ Q, q * z₂ = z₂ * q := hzc z₂ hz₂
  have hz₁ic : ∀ q ∈ Q, q * z₁⁻¹ = z₁⁻¹ * q := hzc _ (Subgroup.inv_mem _ hz₁)
  have hz₂ic : ∀ q ∈ Q, q * z₂⁻¹ = z₂⁻¹ * q := hzc _ (Subgroup.inv_mem _ hz₂)
  have hb1r : b₁ * r⁻¹ = z₁⁻¹ * r⁻¹ * b₁ := by rw [hz₁def]; group
  have hb2p : b₂ * p⁻¹ = z₂⁻¹ * p⁻¹ * b₂ := by rw [hz₂def]; group
  have hb1r' : b₁ * r * b₁⁻¹ = r * z₁ := by rw [hz₁def]; group
  have hb2p' : b₂ * p = p * z₂ * b₂ := by rw [hz₂def]; group
  have e1 : x * b₁ * x⁻¹ = p⁻¹ * b₁ := by rw [hpdef]; group
  have e2 : x * b₂ * x⁻¹ = r⁻¹ * b₂ := by rw [hrdef]; group
  have hF8 : (p⁻¹ * b₁) * (r⁻¹ * b₂) = (r⁻¹ * b₂) * (p⁻¹ * b₁) := by
    rw [← e1, ← e2]
    calc (x * b₁ * x⁻¹) * (x * b₂ * x⁻¹) = x * (b₁ * b₂) * x⁻¹ := by group
      _ = x * (b₂ * b₁) * x⁻¹ := by rw [hb]
      _ = (x * b₂ * x⁻¹) * (x * b₁ * x⁻¹) := by group
  have hL : (p⁻¹ * b₁) * (r⁻¹ * b₂) = z₁⁻¹ * (p⁻¹ * r⁻¹ * b₁ * b₂) := by
    calc (p⁻¹ * b₁) * (r⁻¹ * b₂) = p⁻¹ * (b₁ * r⁻¹) * b₂ := by group
      _ = p⁻¹ * (z₁⁻¹ * r⁻¹ * b₁) * b₂ := by rw [hb1r]
      _ = (p⁻¹ * z₁⁻¹) * (r⁻¹ * b₁ * b₂) := by group
      _ = (z₁⁻¹ * p⁻¹) * (r⁻¹ * b₁ * b₂) := by rw [hz₁ic _ (Q.inv_mem hpQ)]
      _ = z₁⁻¹ * (p⁻¹ * r⁻¹ * b₁ * b₂) := by group
  have hR : (r⁻¹ * b₂) * (p⁻¹ * b₁) = z₂⁻¹ * (r⁻¹ * p⁻¹ * b₂ * b₁) := by
    calc (r⁻¹ * b₂) * (p⁻¹ * b₁) = r⁻¹ * (b₂ * p⁻¹) * b₁ := by group
      _ = r⁻¹ * (z₂⁻¹ * p⁻¹ * b₂) * b₁ := by rw [hb2p]
      _ = (r⁻¹ * z₂⁻¹) * (p⁻¹ * b₂ * b₁) := by group
      _ = (z₂⁻¹ * r⁻¹) * (p⁻¹ * b₂ * b₁) := by rw [hz₂ic _ (Q.inv_mem hrQ)]
      _ = z₂⁻¹ * (r⁻¹ * p⁻¹ * b₂ * b₁) := by group
  have hpr' : p⁻¹ * r⁻¹ = r⁻¹ * p⁻¹ := by
    calc p⁻¹ * r⁻¹ = (r * p)⁻¹ := (mul_inv_rev r p).symm
      _ = (p * r)⁻¹ := by rw [hpr]
      _ = r⁻¹ * p⁻¹ := mul_inv_rev p r
  have hW : p⁻¹ * r⁻¹ * b₁ * b₂ = r⁻¹ * p⁻¹ * b₂ * b₁ := by
    calc p⁻¹ * r⁻¹ * b₁ * b₂ = (p⁻¹ * r⁻¹) * (b₁ * b₂) := by group
      _ = (r⁻¹ * p⁻¹) * (b₂ * b₁) := by rw [hpr', hb]
      _ = r⁻¹ * p⁻¹ * b₂ * b₁ := by group
  have hz : z₁ = z₂ := by
    have h := hF8
    rw [hL, hR, hW] at h
    exact inv_injective (mul_right_cancel h)
  have hψ : (b₁ * b₂) * x * (b₁ * b₂)⁻¹ * x⁻¹ = r * z₁ * p := by
    rw [← hb1r', hpdef, hrdef]
    group
  rw [hψ] at h₁₂
  have hb12Q : b₁ * b₂ ∈ Q := Q.mul_mem hb₁ hb₂
  have hb1pQ : b₁ * p ∈ Q := Q.mul_mem hb₁ hpQ
  have hLHS : (b₁ * b₂) * (r * z₁ * p) = (r * z₁ * (z₁ * z₂)) * (p * (b₁ * b₂)) := by
    calc (b₁ * b₂) * (r * z₁ * p) = b₁ * (b₂ * r) * z₁ * p := by group
      _ = b₁ * (r * b₂) * z₁ * p := by rw [h₂]
      _ = (b₁ * r * b₁⁻¹) * (b₁ * b₂ * z₁) * p := by group
      _ = (r * z₁) * (z₁ * (b₁ * b₂)) * p := by rw [hb1r', hz₁c _ hb12Q]
      _ = (r * z₁) * z₁ * b₁ * (b₂ * p) := by group
      _ = (r * z₁) * z₁ * b₁ * (p * z₂ * b₂) := by rw [hb2p']
      _ = (r * z₁) * z₁ * (b₁ * p * z₂) * b₂ := by group
      _ = (r * z₁) * z₁ * (z₂ * (b₁ * p)) * b₂ := by rw [hz₂c _ hb1pQ]
      _ = (r * z₁) * z₁ * (z₂ * (p * b₁)) * b₂ := by rw [h₁]
      _ = (r * z₁ * (z₁ * z₂)) * (p * (b₁ * b₂)) := by group
  have hRHS : (r * z₁ * p) * (b₁ * b₂) = (r * z₁) * (p * (b₁ * b₂)) := by group
  rw [hLHS, hRHS] at h₁₂
  have hzz : z₁ * z₂ = 1 := mul_eq_left.mp (mul_right_cancel h₁₂)
  rw [← hz] at hzz
  have hz13 : z₁ ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz₁
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
  have hz1 : z₁ = 1 := by
    calc z₁ = z₁ ^ 3 * (z₁ * z₁)⁻¹ := by group
      _ = 1 := by rw [hz13, hzz]; group
  calc b₁ * r = (b₁ * r * b₁⁻¹) * b₁ := by group
    _ = r * b₁ := by rw [hb1r', hz1, mul_one]

omit [Finite G] in
theorem comm_of_mem_of_normalizer {F : Subgroup G} (hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    {b x : G} (hbF : b ∈ F) (hxN : x ∈ Subgroup.normalizer (F : Set G)) :
    b * (b * x * b⁻¹ * x⁻¹) = (b * x * b⁻¹ * x⁻¹) * b := by
  have hψF : b * x * b⁻¹ * x⁻¹ ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hg : x⁻¹ * f * x ∈ F := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) f).mp hf
      rwa [inv_inv] at h
    have hbg : b * (x⁻¹ * f * x) = (x⁻¹ * f * x) * b := hFc _ hbF _ hg
    have hbf : b * f = f * b := hFc _ hbF _ hf
    have hbinvg : b⁻¹ * (x⁻¹ * f * x) = (x⁻¹ * f * x) * b⁻¹ := by
      calc b⁻¹ * (x⁻¹ * f * x) = b⁻¹ * ((x⁻¹ * f * x) * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * (x⁻¹ * f * x)) * b⁻¹ := by rw [hbg]
        _ = (x⁻¹ * f * x) * b⁻¹ := by group
    symm
    calc (b * x * b⁻¹ * x⁻¹) * f = b * x * (b⁻¹ * (x⁻¹ * f * x)) * x⁻¹ := by group
      _ = b * x * ((x⁻¹ * f * x) * b⁻¹) * x⁻¹ := by rw [hbinvg]
      _ = b * f * x * b⁻¹ * x⁻¹ := by group
      _ = f * b * x * b⁻¹ * x⁻¹ := by rw [hbf]
      _ = f * (b * x * b⁻¹ * x⁻¹) := by group
  exact Subgroup.mem_centralizer_iff.mp hψF b hbF

theorem sup_zpowers_eq {A : Subgroup G} (hA3 : ∀ x ∈ A, x ^ 3 = 1) (hA27 : Nat.card A = 27)
    {d b₁ b₂ : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hb₁ : b₁ ∈ A) (hb₂ : b₂ ∈ A)
    (hb₁d : b₁ ∉ Subgroup.zpowers d) (hb₂d : b₂ ∉ Subgroup.zpowers b₁ ⊔ Subgroup.zpowers d) :
    Subgroup.zpowers b₁ ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers b₂ = A := by
  set H₁ := Subgroup.zpowers b₁ ⊔ Subgroup.zpowers d with hH₁
  set H₂ := H₁ ⊔ Subgroup.zpowers b₂ with hH₂
  have hH₁A : H₁ ≤ A := sup_le (Subgroup.zpowers_le.mpr hb₁) (Subgroup.zpowers_le.mpr hdA)
  have hH₂A : H₂ ≤ A := sup_le hH₁A (Subgroup.zpowers_le.mpr hb₂)
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hA3 d hdA) hd1]
  have hlt₁ : Subgroup.zpowers d < H₁ := by
    refine lt_of_le_of_ne le_sup_right fun h => hb₁d ?_
    rw [h]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b₁)
  have hlt₂ : H₁ < H₂ := by
    refine lt_of_le_of_ne le_sup_left fun h => hb₂d ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b₂)
  have c₁ := Subgroup.card_lt_of_lt hlt₁
  have c₂ := Subgroup.card_lt_of_lt hlt₂
  have d₁ : Nat.card H₁ ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA27]
    exact Subgroup.card_dvd_of_le hH₁A
  have d₂ : Nat.card H₂ ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA27]
    exact Subgroup.card_dvd_of_le hH₂A
  obtain ⟨k₁, hk₁, he₁⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp d₁
  obtain ⟨k₂, hk₂, he₂⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp d₂
  rw [hd3, he₁] at c₁
  rw [he₁, he₂] at c₂
  have h27 : Nat.card H₂ = 27 := by
    rw [he₂]
    interval_cases k₁ <;> interval_cases k₂ <;> revert c₁ c₂ <;> norm_num
  exact Subgroup.eq_of_le_of_card_ge hH₂A (by rw [hA27, h27])

theorem false_of_quadratic {A Q D : Subgroup G} {d b₁ b₂ : G}
    (hAe : IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hQX : IsExtra2127 Q) (hQS : IsSylowOf 3 Q (Subgroup.normalizer (A : Set G)))
    (hAQ : A ≤ Q) (hQC : Q ⊓ Subgroup.centralizer (A : Set G) = A)
    (hdc : ∀ q ∈ Q, q * d * q⁻¹ = d) (hb₁ : b₁ ∈ A) (hb₂ : b₂ ∈ A)
    (hb₁d : b₁ ∉ Subgroup.zpowers d) (hb₂d : b₂ ∉ Subgroup.zpowers b₁ ⊔ Subgroup.zpowers d)
    (hDe : IsElemAbelian 3 D) (hD81 : Nat.card D = 81) (hdD : d ∈ D)
    (hQD : Q ≤ Subgroup.normalizer (D : Set G))
    (hP₁' : ∀ x ∈ D, b₁ * (b₁ * x * b₁⁻¹ * x⁻¹) = (b₁ * x * b₁⁻¹ * x⁻¹) * b₁)
    (hP₂' : ∀ x ∈ D, b₂ * (b₂ * x * b₂⁻¹ * x⁻¹) = (b₂ * x * b₂⁻¹ * x⁻¹) * b₂)
    (hP₁₂' : ∀ x ∈ D, (b₁ * b₂) * ((b₁ * b₂) * x * (b₁ * b₂)⁻¹ * x⁻¹) =
      ((b₁ * b₂) * x * (b₁ * b₂)⁻¹ * x⁻¹) * (b₁ * b₂))
    (h729 : Nat.card (Q ⊔ D : Subgroup G) ≤ 729) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hQe, hQ35, -⟩ := hQX
  have hQ243 : Nat.card Q = 243 := by rw [hQ35]; norm_num
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hdQ : d ∈ Q := hAQ hdA
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcommQ := Item2119End2Proof.comm_mem_zpowers hQe hdQ hd1 hd3 hdc
  have hzc : ∀ z ∈ Subgroup.zpowers d, ∀ q ∈ Q, q * z = z * q := by
    intro z hz q hq
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hqd : Commute q d := by
      show q * d = d * q
      calc q * d = q * d * q⁻¹ * q := by group
        _ = d * q := by rw [hdc q hq]
    exact (hqd.zpow_right k).eq
  have hgen := sup_zpowers_eq hAe.2 hA27 hdA hd1 hb₁ hb₂ hb₁d hb₂d
  have hQ3 : IsPGroup 3 Q := hQS.isPGroup
  have hD3 : IsPGroup 3 D := isPGroup_of_pow hDe.2
  have hQD27 : Nat.card (D ⊓ Q : Subgroup G) ≤ 27 := by
    have h := Item2119End3Proof.card_le_of_commute_of_extraspecial hQe hQ243
      (B := (D ⊓ Q).subgroupOf Q) (fun x hx y hy => Subtype.ext
        (hDc _ (Subgroup.mem_subgroupOf.mp hx).1 _ (Subgroup.mem_subgroupOf.mp hy).1))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h
  have hm := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hQD
  rw [hD81, hQ243] at hm
  have hP729 : Nat.card (Q ⊔ D : Subgroup G) = 729 := by
    have h1 : 81 * 243 ≤ Nat.card (D ⊔ Q : Subgroup G) * 27 := by
      rw [← hm]
      exact Nat.mul_le_mul_left _ hQD27
    rw [sup_comm] at h729 ⊢
    omega
  have hP3 : IsPGroup 3 (Q ⊔ D : Subgroup G) := IsPGroup.to_sup_of_normal_right' hQ3 hD3 hQD
  have hQn : Q ⊔ D ≤ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_of_card le_sup_left hP3 (by rw [hP729, hQ243])
  have hDA : D ≤ Subgroup.normalizer (A : Set G) := by
    intro x hx
    have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := hQn (Subgroup.mem_sup_right hx)
    have hψQ : ∀ b ∈ A, b * x * b⁻¹ * x⁻¹ ∈ Q := by
      intro b hb
      have h1 : x * b⁻¹ * x⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hxQ _).mp (Q.inv_mem (hAQ hb))
      have h2 : b * x * b⁻¹ * x⁻¹ = b * (x * b⁻¹ * x⁻¹) := by group
      rw [h2]
      exact Q.mul_mem (hAQ hb) h1
    have hψD : ∀ b ∈ A, b * x * b⁻¹ * x⁻¹ ∈ D := by
      intro b hb
      have h1 : b * x * b⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hQD (hAQ hb)) _).mp hx
      exact D.mul_mem h1 (D.inv_mem hx)
    have hP₁ := hP₁' x hx
    have hP₂ := hP₂' x hx
    have hP₁₂ := hP₁₂' x hx
    have hb₁₂ := hAc b₁ hb₁ b₂ hb₂
    have hP₂₁ : (b₂ * b₁) * ((b₂ * b₁) * x * (b₂ * b₁)⁻¹ * x⁻¹) =
        ((b₂ * b₁) * x * (b₂ * b₁)⁻¹ * x⁻¹) * (b₂ * b₁) := by
      rw [← hb₁₂]
      exact hP₁₂
    have h12 : b₁ * (b₂ * x * b₂⁻¹ * x⁻¹) = (b₂ * x * b₂⁻¹ * x⁻¹) * b₁ :=
      comm_of_relations hd3 hzc hcommQ (hAQ hb₁) (hAQ hb₂) (hψQ b₁ hb₁) (hψQ b₂ hb₂) rfl rfl
        hb₁₂ (hDc _ (hψD b₁ hb₁) _ (hψD b₂ hb₂)) hP₁ hP₂ hP₁₂
    have h21 : b₂ * (b₁ * x * b₁⁻¹ * x⁻¹) = (b₁ * x * b₁⁻¹ * x⁻¹) * b₂ :=
      comm_of_relations hd3 hzc hcommQ (hAQ hb₂) (hAQ hb₁) (hψQ b₂ hb₂) (hψQ b₁ hb₁) rfl rfl
        hb₁₂.symm (hDc _ (hψD b₂ hb₂) _ (hψD b₁ hb₁)) hP₂ hP₁ hP₂₁
    have hcent : ∀ g ∈ Q, b₁ * g = g * b₁ → b₂ * g = g * b₂ → g ∈ A := by
      intro g hg h₁ h₂
      have hdg : d * g = g * d := (hzc d (Subgroup.mem_zpowers d) g hg).symm
      have hle : A ≤ Subgroup.centralizer ({g} : Set G) := by
        rw [← hgen]
        refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le] <;>
          exact Subgroup.mem_centralizer_singleton_iff.mpr ‹_›
      rw [← hQC]
      exact ⟨hg, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hy)⟩
    have hψ₁ := hcent _ (hψQ b₁ hb₁) hP₁ h21
    have hψ₂ := hcent _ (hψQ b₂ hb₂) h12 hP₂
    have hconj : ∀ b ∈ A, b * x * b⁻¹ * x⁻¹ ∈ A → x * b * x⁻¹ ∈ A := by
      intro b hb hψ
      have h1 : x * b * x⁻¹ = (b * x * b⁻¹ * x⁻¹)⁻¹ * b := by group
      rw [h1]
      exact A.mul_mem (A.inv_mem hψ) hb
    have hxd : x * d * x⁻¹ = d := by
      rw [hDc x hx d hdD]
      group
    have hle : Subgroup.zpowers b₁ ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers b₂ ≤
        A.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_comap] <;>
        show x * _ * x⁻¹ ∈ _
      · exact hconj b₁ hb₁ hψ₁
      · rw [hxd]
        exact hdA
      · exact hconj b₂ hb₂ hψ₂
    rw [hgen] at hle
    refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    have h1 := hle hb
    rw [Subgroup.mem_comap] at h1
    exact h1
  have hle := Item2119End6Proof.card_le_three_pow_of_isPGroup (sup_le hQS.le hDA) hP3
  rw [← hQS.card_eq, hP729, hQ243] at hle
  omega

theorem false_of_three {A Q D F₁ F₂ F₁₂ : Subgroup G} {d b₁ b₂ : G}
    (hAe : IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hQX : IsExtra2127 Q) (hQS : IsSylowOf 3 Q (Subgroup.normalizer (A : Set G)))
    (hAQ : A ≤ Q) (hQC : Q ⊓ Subgroup.centralizer (A : Set G) = A)
    (hdc : ∀ q ∈ Q, q * d * q⁻¹ = d) (hb₁ : b₁ ∈ A) (hb₂ : b₂ ∈ A)
    (hb₁d : b₁ ∉ Subgroup.zpowers d) (hb₂d : b₂ ∉ Subgroup.zpowers b₁ ⊔ Subgroup.zpowers d)
    (hF₁ : b₁ ∈ F₁) (hF₂ : b₂ ∈ F₂) (hF₁₂ : b₁ * b₂ ∈ F₁₂)
    (hF₁c : ∀ x ∈ F₁, ∀ y ∈ F₁, x * y = y * x) (hF₂c : ∀ x ∈ F₂, ∀ y ∈ F₂, x * y = y * x)
    (hF₁₂c : ∀ x ∈ F₁₂, ∀ y ∈ F₁₂, x * y = y * x)
    (hDe : IsElemAbelian 3 D) (hD81 : Nat.card D = 81) (hdD : d ∈ D)
    (hQD : Q ≤ Subgroup.normalizer (D : Set G))
    (hD₁ : D ≤ Subgroup.normalizer (F₁ : Set G)) (hD₂ : D ≤ Subgroup.normalizer (F₂ : Set G))
    (hD₁₂ : D ≤ Subgroup.normalizer (F₁₂ : Set G))
    (h729 : Nat.card (Q ⊔ D : Subgroup G) ≤ 729) : False :=
  false_of_quadratic hAe hA27 hdA hd1 hQX hQS hAQ hQC hdc hb₁ hb₂ hb₁d hb₂d hDe hD81 hdD hQD
    (fun _ hx => comm_of_mem_of_normalizer hF₁c hF₁ (hD₁ hx))
    (fun _ hx => comm_of_mem_of_normalizer hF₂c hF₂ (hD₂ hx))
    (fun _ hx => comm_of_mem_of_normalizer hF₁₂c hF₁₂ (hD₁₂ hx)) h729

theorem not_config2119Fix {A E U L U₀ X : Subgroup G} {c d a : G} {Lf F : G → Subgroup G}
    {D : Subgroup G} (h : Config2119Fix G A E U c L d U₀ a X Lf F D) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE := h.cfg
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 : d ≠ 1 := hE.ne_one_d
  obtain ⟨haA, had⟩ := Item2119End7Proof.mem_a_not_mem hE
  have hpairs := mem_lThreeStarPairs_iff.mp hE.cfg.pair.mem_pair
  have hcA : c ∈ A := hE.cfg.pair.mem_E.2 hpairs.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  obtain ⟨eL⟩ := h.l34
  have hZ : Subgroup.center (lBar L) = ⊥ :=
    Item2119End3Proof.center_eq_bot_of_mulEquiv' eL
      (Item21Early2Proof.center_projSL_three_eq_bot (by norm_num) (by decide))
  have hcL : c ∉ L := Item2119End3Proof.not_mem_of_mem_thetaComponentsAt hLc hZ
    (hAe.2 c hcA) hpairs.2.1
  have hcd : c ∉ Subgroup.zpowers d := fun h1 => hcL ((Subgroup.zpowers_le.mpr hE.mem_d.2) h1)
  have hacd : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d :=
    Item2119EndProof.not_mem_sup_of_config2119End hE
  have hcaA : c * a ∈ A := A.mul_mem hcA haA
  have hcad : c * a ∉ Subgroup.zpowers d := fun h1 => hacd (by
    have : a = c⁻¹ * (c * a) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)))
      (Subgroup.mem_sup_right h1))
  set Q := q2127Of A d F with hQdef
  have hAFQ : ∀ b ∈ A, b ∉ Subgroup.zpowers d → A ⊔ F b ≤ Q := fun b hb hbd =>
    le_iSup₂_of_le (f := fun e (_ : e ∈ {e : G | e ∈ A ∧ e ∉ Subgroup.zpowers d}) => A ⊔ F e)
      b ⟨hb, hbd⟩ le_rfl
  have hAQ : A ≤ Q := le_sup_left.trans (hAFQ a haA had)
  have hdc : ∀ q ∈ Q, q * d * q⁻¹ = d := by
    intro q hq
    have hQN : Q ≤ Subgroup.normalizer (A : Set G) := h.q.1.le
    have hmem : A.normalizerMonoidHom ⟨q, hQN hq⟩ ∈ starOf A Q :=
      ⟨⟨q, hQN hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rw [h.q.2.2.1] at hmem
    have h1 := (mem_fixOn_iff.mp hmem.2) ⟨d, hdA⟩ (Subgroup.mem_zpowers d)
    exact congrArg Subtype.val h1
  have hFc : ∀ b ∈ A, b ∉ Subgroup.zpowers d → ∀ x ∈ F b, ∀ y ∈ F b, x * y = y * x :=
    fun b hb hbd x hx y hy =>
      congrArg Subtype.val ((h.f b hb hbd).1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbF : ∀ b ∈ A, b ∉ Subgroup.zpowers d → b ∈ F b := fun b hb hbd =>
    mem_F hAe hA27 h.syl h.q h.f hb hbd
  obtain ⟨P, hP⟩ :=
    CFSG.ABGLocalTools.exists_isSylowOf 3 (y2128Of (Lf a) (F a) Q)
  obtain ⟨-, hDe, hD81, hYD, hFL⟩ := h.c29 a haA had P hP
  have hDY : ∀ b ∈ A, b ∉ Subgroup.zpowers d → D ≤ y2128Of (Lf b) (F b) Q := by
    intro b hb hbd
    obtain ⟨Pb, hPb⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (y2128Of (Lf b) (F b) Q)
    rw [← (h.c29 b hb hbd Pb hPb).1]
    exact (thompsonSubgroup_le Pb).trans hPb.le
  have hdF : d ∈ F a := Item2119End2Proof.mem_of_isQOf2127 hA27 (h.f a haA had).2.1
    (hFc a haA had) (hAFQ a haA had) (h.q.2.2.2.2 a haA had).1 h.q.2.1 hdA hdc
  have hdD : d ∈ D := hFL a haA had ⟨hdF, (h.lf a haA had).2.2.2.2.1⟩
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) := le_sup_right.trans hYD
  have hDF : ∀ b ∈ A, b ∉ Subgroup.zpowers d → D ≤ Subgroup.normalizer (F b : Set G) :=
    fun b hb hbd => (hDY b hb hbd).trans (h.c28 b hb hbd).1
  have hP3 : IsPGroup 3 (Q ⊔ D : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' h.q.1.isPGroup (isPGroup_of_pow hDe.2) hQD
  have h729 : Nat.card (Q ⊔ D : Subgroup G) ≤ 729 :=
    card_le_729 hAe hA27 h.syl h.q h.f h.c28 haA had hP3
      (sup_le le_sup_right (hDY a haA had))
  exact false_of_three hAe hA27 hdA hd1 h.extra h.q.1 hAQ h.q.2.1 hdc hcA haA hcd hacd
    (hbF c hcA hcd) (hbF a haA had) (hbF _ hcaA hcad) (hFc c hcA hcd) (hFc a haA had)
    (hFc _ hcaA hcad) hDe hD81 hdD hQD (hDF c hcA hcd) (hDF a haA had) (hDF _ hcaA hcad) h729

end Item2119End8Proof

open Item2119End8Proof

theorem item2119FinalFix_holds : Item2119FinalFix :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => not_config2119Fix h

@[expose] def Item2119EndLoc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        ∀ F : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d →
            CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G))) →
          IsQOf2127 A d F → IsExtra2127 (q2127Of A d F) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ P : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
            Concl2129Loc (Lf e) (F e) (y2128Of (Lf e) (F e) (q2127Of A d F)) P) →
            False

theorem item2129Same_iff_endLoc : Item2129Same ↔ Item2119EndLoc := by
  constructor
  · intro hSame G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hS := hSame G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL
    obtain ⟨haA, had⟩ := Item2119End7Proof.mem_a_not_mem hE
    obtain ⟨P₀, hP₀⟩ :=
      CFSG.ABGLocalTools.exists_isSylowOf 3 (y2128Of (Lf a) (F a) (q2127Of A d F))
    refine not_config2119Fix (D := CFSG.Open.thompsonSubgroup P₀)
      ⟨hE, h23, h24, hLf, h26, hF, h27, hQ, hQX, h28, fun e he hed P hP => ?_⟩
    have hJ : CFSG.Open.thompsonSubgroup P = CFSG.Open.thompsonSubgroup P₀ :=
      hS e he hed a haA had P P₀ hP hP₀
    obtain ⟨h1, h2, h3, -⟩ := hL e he hed P hP
    rw [hJ] at h1 h2 h3
    refine ⟨hJ, h1, h2, h3, fun b hb hbd => ?_⟩
    obtain ⟨Pb, hPb⟩ :=
      CFSG.ABGLocalTools.exists_isSylowOf 3 (y2128Of (Lf b) (F b) (q2127Of A d F))
    rw [← hS b hb hbd a haA had Pb P₀ hPb hP₀]
    exact (hL b hb hbd Pb hPb).2.2.2
  · intro h G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL
    exact (h G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL).elim

end CFSG.RankThree.PartTwo.Sec21
