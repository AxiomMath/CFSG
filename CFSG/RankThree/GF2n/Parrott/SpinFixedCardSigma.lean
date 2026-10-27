module

public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardMore
public import CFSG.RankThree.GF2n.Parrott.QA45SigmaCentralizers
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.RankThree.GF2n.Parrott.LiftOrderThree
public import CFSG.RankThree.GF2n.Parrott.SpinWords

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.ABGLocalTools


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uvA" => uA * vA

namespace SpinFixedCardSigma

open SpinWords

private def sigmaWord : List ℕ :=
  [0, 1, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 1,
    1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 1]

private def sigmaTWord : List ℕ :=
  [1, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 1, 1, 1, 2, 1, 0, 1]

private def sigmaUVWord : List ℕ := [1, 2, 1, 2, 1, 2, 1, 0]

private def sigmaTUVWord : List ℕ := [1, 2, 1, 2, 1, 2, 1]

private theorem sigma_eq : s1A * s2A⁻¹ = wordElem sigmaWord := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_wordElem]
  show sigma1 * sigma2⁻¹ = wordPerm sigmaWord
  decide +kernel

private theorem sigma_mul_t_eq : s1A * s2A⁻¹ * tA = wordElem sigmaTWord := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_wordElem]
  show sigma1 * sigma2⁻¹ * x45 = wordPerm sigmaTWord
  decide +kernel

private theorem sigma_mul_uv_eq : s1A * s2A⁻¹ * uvA = wordElem sigmaUVWord := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_wordElem]
  show sigma1 * sigma2⁻¹ * (u * v) = wordPerm sigmaUVWord
  decide +kernel

private theorem sigma_mul_t_uv_eq : s1A * s2A⁻¹ * (tA * uvA) = wordElem sigmaTUVWord := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_wordElem]
  show sigma1 * sigma2⁻¹ * (x45 * (u * v)) = wordPerm sigmaTUVWord
  decide +kernel

private theorem fixCard_sigmaWord : fixCard (wordMat sigmaWord) = 16 := by
  decide +kernel

private theorem fixCard_sigmaTWord : fixCard (wordMat sigmaTWord) = 4 := by
  decide +kernel

private theorem fixCard_sigmaUVWord : fixCard (wordMat sigmaUVWord) = 4 := by
  decide +kernel

private theorem fixCard_sigmaTUVWord : fixCard (wordMat sigmaTUVWord) = 4 := by
  decide +kernel

private theorem mem_closure_t_uv_iff (x : A45) :
    x ∈ Subgroup.closure ({tA, uvA} : Set A45) ↔
      x = 1 ∨ x = tA ∨ x = uvA ∨ x = tA * uvA := by
  constructor
  · intro hx
    let S : Subgroup A45 :=
      { carrier := {y | y = 1 ∨ y = tA ∨ y = uvA ∨ y = tA * uvA}
        one_mem' := Or.inl rfl
        mul_mem' := by
          intro y z hy hz
          simp only [Set.mem_setOf_eq] at hy hz ⊢
          rcases hy with rfl | rfl | rfl | rfl <;>
            rcases hz with rfl | rfl | rfl | rfl <;>
            simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one,
              Subtype.coe_mk] <;>
            decide +kernel
        inv_mem' := by
          intro y hy
          simp only [Set.mem_setOf_eq] at hy ⊢
          rcases hy with rfl | rfl | rfl | rfl <;>
            simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one,
              Subtype.coe_mk] <;>
            decide +kernel }
    have hle : Subgroup.closure ({tA, uvA} : Set A45) ≤ S := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    exact hle hx
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

private abbrev Csigma : Subgroup A45 := Subgroup.centralizer ({(s1A * s2A⁻¹)} : Set A45)

private abbrev E4 : Subgroup A45 := Subgroup.closure ({tA, uvA} : Set A45)

private theorem card_centralizer_s1s2inv :
    Nat.card (Subgroup.centralizer ({(s1A * s2A⁻¹)} : Set A45)) = 108 := by
  have hm : sigma1 * sigma2⁻¹ ∈ QA45.originalSubgroup :=
    QA45.originalSubgroup.mul_mem sigma1_mem_A (QA45.originalSubgroup.inv_mem sigma2_mem_A)
  exact (card_centralizer_QA45_eq_filter (sigma1 * sigma2⁻¹) hm).trans
    Certificates.certificate946005.centralizer_sigma1sigma2inv

end SpinFixedCardSigma

theorem spinFixedCard_sigma1_mul_sigma2_inv :
    fixCard (((rhoA ((⟨sigma1, sigma1_mem_A⟩ : ↥QA45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_A⟩ : ↥QA45.originalSubgroup)⁻¹) :
        Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))) = 16 := by
  rw [SpinFixedCardSigma.sigma_eq, SpinWords.rhoA_wordElem]
  exact SpinFixedCardSigma.fixCard_sigmaWord

theorem spinFixedCard_sigma1_mul_sigma2_inv_mul {b : ↥QA45.originalSubgroup}
    (hb : b ∈ Subgroup.closure {(⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup),
      (⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup) * (⟨v, v_mem_A⟩ : ↥QA45.originalSubgroup)})
    (hb1 : b ≠ 1) :
    fixCard (((rhoA ((⟨sigma1, sigma1_mem_A⟩ : ↥QA45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_A⟩ : ↥QA45.originalSubgroup)⁻¹ * b) :
        Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))) = 4 := by
  rcases (SpinFixedCardSigma.mem_closure_t_uv_iff b).1 hb with h | h | h | h
  · exact absurd h hb1
  · rw [h, SpinFixedCardSigma.sigma_mul_t_eq, SpinWords.rhoA_wordElem]
    exact SpinFixedCardSigma.fixCard_sigmaTWord
  · rw [h, SpinFixedCardSigma.sigma_mul_uv_eq, SpinWords.rhoA_wordElem]
    exact SpinFixedCardSigma.fixCard_sigmaUVWord
  · rw [h, SpinFixedCardSigma.sigma_mul_t_uv_eq, SpinWords.rhoA_wordElem]
    exact SpinFixedCardSigma.fixCard_sigmaTUVWord

theorem exists_conj_mem_closure_t_uv_of_mem_centralizer
    {a : ↥QA45.originalSubgroup}
    (ha : a ∈ Subgroup.centralizer ({(⟨sigma1, sigma1_mem_A⟩ : ↥QA45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_A⟩ : ↥QA45.originalSubgroup)⁻¹} : Set ↥QA45.originalSubgroup))
    (h2 : ∃ k : ℕ, orderOf a = 2 ^ k) :
    ∃ c ∈ Subgroup.centralizer ({(⟨sigma1, sigma1_mem_A⟩ : ↥QA45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_A⟩ : ↥QA45.originalSubgroup)⁻¹} : Set ↥QA45.originalSubgroup),
      c * a * c⁻¹ ∈ Subgroup.closure {(⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup),
        (⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup) * (⟨v, v_mem_A⟩ : ↥QA45.originalSubgroup)} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hEle, _, hEcard⟩ := qa45_sigma_centralizer_sylow.2.1
  have hCcard : Nat.card SpinFixedCardSigma.Csigma = 108 := by
    show Nat.card (Subgroup.centralizer ({(s1A * s2A⁻¹)} : Set A45)) = 108
    exact SpinFixedCardSigma.card_centralizer_s1s2inv
  have hEleC : SpinFixedCardSigma.E4 ≤ SpinFixedCardSigma.Csigma := by
    show Subgroup.closure ({tA, uvA} : Set A45) ≤
      Subgroup.centralizer ({(s1A * s2A⁻¹)} : Set A45)
    exact hEle
  have hEsyl : IsSylowOf 2 SpinFixedCardSigma.E4 SpinFixedCardSigma.Csigma :=
    isSylowOf_of_card hEleC (by
      show Nat.card (Subgroup.closure ({tA, uvA} : Set A45)) =
        2 ^ (Nat.card (Subgroup.centralizer ({(s1A * s2A⁻¹)} : Set A45))).factorization 2
      rw [hEcard, hCcard]
      decide +kernel)
  obtain ⟨k, hk⟩ := h2
  have hAcard : Nat.card (Subgroup.zpowers (⟨a, ha⟩ : SpinFixedCardSigma.Csigma)) = 2 ^ k := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk]
    exact hk
  have hApg : IsPGroup 2 (Subgroup.zpowers (⟨a, ha⟩ : SpinFixedCardSigma.Csigma)) :=
    IsPGroup.of_card hAcard
  obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow hApg
  have hSsyl : IsSylowOf 2
      ((S : Subgroup SpinFixedCardSigma.Csigma).map SpinFixedCardSigma.Csigma.subtype)
      SpinFixedCardSigma.Csigma := ⟨S, rfl⟩
  obtain ⟨c, hcC, hconj⟩ := IsSylowOf.exists_mem_conj hEsyl hSsyl
  have haS : (⟨a, ha⟩ : SpinFixedCardSigma.Csigma) ∈ S := hAS (Subgroup.mem_zpowers _)
  have haS' : a ∈ (S : Subgroup SpinFixedCardSigma.Csigma).map
      SpinFixedCardSigma.Csigma.subtype := ⟨⟨a, ha⟩, haS, rfl⟩
  refine ⟨c⁻¹, ?_, ?_⟩
  · change c⁻¹ ∈ SpinFixedCardSigma.Csigma
    exact SpinFixedCardSigma.Csigma.inv_mem hcC
  · change c⁻¹ * a * (c⁻¹)⁻¹ ∈ SpinFixedCardSigma.E4
    simpa using (hconj a).1 haS'

end CFSG.RankThree.GF2n.Parrott
