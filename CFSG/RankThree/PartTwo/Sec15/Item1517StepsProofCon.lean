module

public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

@[expose] def Step1517Q0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A)

variable {G : Type} [Group G] [Finite G]

namespace Proof1517

theorem le_of_le_normalizer_of_cover {L Y Y₁ : Subgroup G} (hY3 : Y = oPrimeResidualOf 3 Y)
    (hcov : Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y) (hLY₁ : L ≤ Y₁)
    (hYN : Y ≤ Subgroup.normalizer (Y₁ : Set G)) : Y ≤ Y₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 Y with hO
  set K := (Y ⊓ Y₁).subgroupOf Y with hK
  have hKn : K.Normal := by
    refine ⟨fun k hk y => ?_⟩
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp hk
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Y.mul_mem (Y.mul_mem y.2 hk1) (Y.inv_mem y.2)
    · exact (Subgroup.mem_normalizer_iff.mp (hYN y.2) k).mp hk2
  have hOn : L ⊓ Y ≤ Subgroup.normalizer (O : Set G) :=
    inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hdecomp : ∀ y ∈ Y, ∃ a ∈ L ⊓ Y, ∃ t ∈ O, a * t = y := by
    intro y hy
    have hy2 : y ∈ (L ⊓ Y) ⊔ O := by rw [← hcov]; exact hy
    have hy' : y ∈ ((L ⊓ Y : Subgroup G) : Set G) * (O : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hOn]
      exact hy2
    obtain ⟨a, ha, t, ht, rfl⟩ := hy'
    exact ⟨a, ha, t, ht, rfl⟩
  have h3K : ∀ x : ↥Y, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ∈ K := by
    rintro x ⟨k, hk⟩
    obtain ⟨a, ha, t, ht, hat⟩ := hdecomp x x.2
    obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) ⟨t, ht⟩
    have htY : t ∈ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y ht
    have hj' : (⟨t, htY⟩ : ↥Y) ^ 2 ^ j = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hj
    have haK : (⟨a, (Subgroup.mem_inf.mp ha).2⟩ : ↥Y) ∈ K := by
      rw [hK, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp ha).2, hLY₁ (Subgroup.mem_inf.mp ha).1⟩
    have hx : QuotientGroup.mk' K x = QuotientGroup.mk' K ⟨t, htY⟩ := by
      have hxe : x = ⟨a, (Subgroup.mem_inf.mp ha).2⟩ * ⟨t, htY⟩ := Subtype.ext hat.symm
      rw [hxe, map_mul]
      have h1 : QuotientGroup.mk' K (⟨a, (Subgroup.mem_inf.mp ha).2⟩ : ↥Y) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr haK
      rw [h1, one_mul]
    have h2 : QuotientGroup.mk' K x ^ 2 ^ j = 1 := by rw [hx, ← map_pow, hj', map_one]
    have h3 : QuotientGroup.mk' K x ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
    have h1 : QuotientGroup.mk' K x = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow _ _ (by norm_num)) (orderOf_dvd_of_pow_eq_one h2)
        (orderOf_dvd_of_pow_eq_one h3))
    exact (QuotientGroup.eq_one_iff x).mp h1
  intro y hy
  rw [hY3] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxK : x ∈ K := (Subgroup.closure_le K).mpr (fun z hz => h3K z hz) hx
  rw [hK, Subgroup.mem_subgroupOf] at hxK
  exact (Subgroup.mem_inf.mp hxK).2

end Proof1517

open Proof1517

theorem step1517Con_of (h153 : Item153MainR) (hobs : Claim153ObsR) (h1411 : Item1411_1R)
    (hq0 : Step1517Q0) : Step1517Con := by
  intro G _ _ A c L h Y hctx Y₀ hY₀ _ hLY₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀, hS₀Y₀⟩ :=
    Sec16.exists_qStar_le_normalizer (h153 G A c L h) (hobs G A c L h) hY₀
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hOQ : O ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hq0 G A c L h Y hctx, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two O).mpr hO2⟩
  obtain ⟨w, hw, hOw⟩ := Sec16.exists_conj_le_normalizer (h1411 G A c L h) hS₀ hS₀Y₀ hOQ
  set Y₁ := Y₀.map (MulAut.conj w).toMonoidHom with hY₁def
  have hY₁ : Y₁ ∈ scriptY0Star A (lB A) := Sec16.map_conj_mem_scriptY0Star hw hY₀
  obtain ⟨-, -, -, -, -, -, hYL, -, hΩ⟩ := hctx.concl1515
  obtain ⟨-, h9, -⟩ := point_facts h hctx
  have h3 : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hwL : w ∈ Subgroup.normalizer (L : Set G) :=
    Sec16.normalizer_zpowers_le_normalizer_L h h3 (normalizer_le_of_omegaA_eq hΩ hw)
  have hLY₁ : L ≤ Y₁ := by
    rw [← Late.map_conj_eq_of_mem_normalizer hwL, hY₁def]
    exact Subgroup.map_mono hLY₀
  have hYN : Y ≤ Subgroup.normalizer (Y₁ : Set G) := by
    rw [hYL]
    exact sup_le (inf_le_left.trans (hLY₁.trans Subgroup.le_normalizer)) hOw
  have hYY₁ : Y ≤ Y₁ := le_of_le_normalizer_of_cover hctx.mem_y0Star.prop.1.2.1 hYL hLY₁ hYN
  have hYeq : Y = Y₁ := hctx.mem_y0Star.eq_of_le hY₁.prop hYY₁
  exact hctx.not_le (hYeq ▸ hLY₁)

end CFSG.RankThree.PartTwo.Sec15
