module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallC
import CFSG.ClassicalInvolution.Q3.Q3TIYRk1
import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2All
public import CFSG.ClassicalInvolution.RouteD.MultiStarModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.MuTab
open CFSG.ClassicalInvolution.Q3.Q3TIY
open scoped MatrixGroups

theorem false_of_three_commuting_padic {Y : Type*} [Group Y] [Finite Y]
    {A B C : Subgroup Y} (cAB : Commutes A B) (cAC : Commutes A C) (cBC : Commutes B C)
    (zA : Nat.card (Subgroup.center A) ∣ 2) (zB : Nat.card (Subgroup.center B) ∣ 2)
    {s : ℕ} (hs : 3 ≤ s)
    (hA : padicValNat 2 (Nat.card A) = s) (hB : padicValNat 2 (Nat.card B) = s)
    (hC : padicValNat 2 (Nat.card C) = s)
    (hY : padicValNat 2 (Nat.card Y) ≤ 2 * s) : False := by
  have hdvd : Nat.card A * Nat.card B * Nat.card C ∣ 4 * Nat.card Y := by
    simpa using card_mul_dvd_of_commute_triple (Q := ⊤) le_top le_top le_top cAB cAC cBC zA zB
  have h2A : 2 ^ s ∣ Nat.card A := by rw [← hA]; exact pow_padicValNat_dvd
  have h2B : 2 ^ s ∣ Nat.card B := by rw [← hB]; exact pow_padicValNat_dvd
  have h2C : 2 ^ s ∣ Nat.card C := by rw [← hC]; exact pow_padicValNat_dvd
  have h2prod : 2 ^ (3 * s) ∣ Nat.card A * Nat.card B * Nat.card C := by
    have h := Nat.mul_dvd_mul (Nat.mul_dvd_mul h2A h2B) h2C
    have hp : 2 ^ s * 2 ^ s * 2 ^ s = 2 ^ (3 * s) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    rw [← hp]
    exact h
  have hdiv : 2 ^ (3 * s) ∣ 4 * Nat.card Y := h2prod.trans hdvd
  have h4ne : 4 * Nat.card Y ≠ 0 := Nat.mul_ne_zero (by norm_num) (Nat.card_pos.ne')
  have hle : 3 * s ≤ padicValNat 2 (4 * Nat.card Y) :=
    (padicValNat_dvd_iff_le (p := 2) h4ne).mp hdiv
  rw [padicValNat.mul (by norm_num) (Nat.card_pos.ne')] at hle
  have h4 : padicValNat 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  rw [h4] at hle
  omega

theorem padicValNat_card_sl2 (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) :
    padicValNat 2 (Nat.card SL(2, GaloisField p e)) =
      padicValNat 2 ((p ^ e) ^ 2 - 1) := by
  have hcardF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hcard : Nat.card SL(2, GaloisField p e) = p ^ e * ((p ^ e) ^ 2 - 1) := by
    rw [card_sl2_field, hcardF]
  have hodd : Odd (p ^ e) := odd_pow_of_ne_two p hp2 e
  have hne : (p ^ e) ^ 2 - 1 ≠ 0 := by
    have h2 : 2 ≤ p ^ e := by
      calc 2 ≤ p := (Fact.out : p.Prime).two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right (by have := (Fact.out : p.Prime).two_le; omega) he
    have : 1 < (p ^ e) ^ 2 := by nlinarith
    omega
  rw [hcard, padicValNat.mul (pow_ne_zero e (Fact.out : p.Prime).ne_zero) hne,
    padicValNat_two_of_odd hodd, zero_add]

theorem padicValNat_card_sl2_three (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) :
    padicValNat 2 (Nat.card SL(2, GaloisField p (3 * e))) =
      padicValNat 2 ((p ^ e) ^ 2 - 1) := by
  rw [padicValNat_card_sl2 p (3 * e) hp2 (by omega)]
  have hpow : (p ^ (3 * e)) ^ 2 = ((p ^ e) ^ 2) ^ 3 := by
    rw [show 3 * e = e * 3 by ring, pow_mul]
    ring
  rw [hpow]
  refine padicValNat_two_cube_sub_one (x := (p ^ e) ^ 2)
    (odd_pow_of_ne_two p hp2 e |>.pow) ?_
  have h2 : 2 ≤ p ^ e := by
    calc 2 ≤ p := (Fact.out : p.Prime).two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by have := (Fact.out : p.Prime).two_le; omega) he
  nlinarith

theorem center_card_dvd_two_of_equiv_sl2 {X F : Type*} [Group X] [Field F] [Finite F]
    {A : Subgroup X} (e : A ≃* SL(2, F)) : Nat.card (Subgroup.center A) ∣ 2 := by
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact card_center_sl2_dvd_two


theorem padicValNat_card_modelFund_g2d4 {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {n e : ℕ}
    (hp2 : p ≠ 2) (ht : t = .G2 ∨ t = .trialityD4)
    (hadm : StatedLieAdmissible t n p e)
    {A : Subgroup (modelUniv t n p e Fact.out).K} (hA : A ∈ ModelFund p t n e) :
    padicValNat 2 (Nat.card A) = padicValNat 2 ((p ^ e) ^ 2 - 1) := by
  have hfund : IsFundTag t := by rcases ht with rfl | rfl <;> trivial
  rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups hp2 hfund hadm hA with
    h | ⟨-, h⟩
  · obtain ⟨eA⟩ := h
    rw [Nat.card_congr eA.toEquiv]
    exact padicValNat_card_sl2 p e hp2 hadm.2.1
  · obtain ⟨eA⟩ := h
    rw [Nat.card_congr eA.toEquiv]
    exact padicValNat_card_sl2_three p e hp2 hadm.2.1

theorem center_card_dvd_two_modelFund_g2d4 {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {n e : ℕ}
    (hp2 : p ≠ 2) (ht : t = .G2 ∨ t = .trialityD4)
    (hadm : StatedLieAdmissible t n p e)
    {A : Subgroup (modelUniv t n p e Fact.out).K} (hA : A ∈ ModelFund p t n e) :
    Nat.card (Subgroup.center A) ∣ 2 := by
  have hfund : IsFundTag t := by rcases ht with rfl | rfl <;> trivial
  rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups hp2 hfund hadm hA with
    h | ⟨-, h⟩
  · obtain ⟨eA⟩ := h
    exact center_card_dvd_two_of_equiv_sl2 eA
  · obtain ⟨eA⟩ := h
    exact center_card_dvd_two_of_equiv_sl2 eA

theorem no_three_g2d4 {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {n e : ℕ}
    (hp2 : p ≠ 2) (ht : t = .G2 ∨ t = .trialityD4)
    (hadm : StatedLieAdmissible t n p e)
    {A B C : Subgroup (modelUniv t n p e Fact.out).K}
    (hA : A ∈ ModelFund p t n e) (hB : B ∈ ModelFund p t n e) (hC : C ∈ ModelFund p t n e)
    (cAB : Commutes A B) (cAC : Commutes A C) (cBC : Commutes B C) : False := by
  let s := padicValNat 2 ((p ^ e) ^ 2 - 1)
  have hs3 : 3 ≤ s := by
    have hodd : Odd (p ^ e) := odd_pow_of_ne_two p hp2 e
    have h8 : 2 ^ 3 ∣ (p ^ e) ^ 2 - 1 := by
      simpa using eight_dvd_sq_sub_one hodd
    have hne : (p ^ e) ^ 2 - 1 ≠ 0 := by
      have h2 : 2 ≤ p ^ e := by
        calc 2 ≤ p := (Fact.out : p.Prime).two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ e := Nat.pow_le_pow_right (by have := (Fact.out : p.Prime).two_le; omega) hadm.2.1
      have : 1 < (p ^ e) ^ 2 := by nlinarith
      omega
    exact (padicValNat_dvd_iff_le (p := 2) hne).mp h8
  have hY : padicValNat 2 (Nat.card (modelUniv t n p e Fact.out).K) ≤ 2 * s := by
    rw [padicValNat_card_modelUniv p e hp2 ht n hadm.2.1]
  have : Finite (modelUniv t n p e Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out (by rcases ht with rfl | rfl <;> trivial) hadm
  exact false_of_three_commuting_padic cAB cAC cBC
    (center_card_dvd_two_modelFund_g2d4 hp2 ht hadm hA)
    (center_card_dvd_two_modelFund_g2d4 hp2 ht hadm hB)
    hs3
    (padicValNat_card_modelFund_g2d4 hp2 ht hadm hA)
    (padicValNat_card_modelFund_g2d4 hp2 ht hadm hB)
    (padicValNat_card_modelFund_g2d4 hp2 ht hadm hC)
    hY

theorem no_three_commuting_modelFund_of_funTwo {p : ℕ} [Fact p.Prime] {t : StatedLieTag}
    {n e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p e) (ht : FunTwoType t n)
    {A B C : Subgroup (modelUniv t n p e Fact.out).K}
    (hA : A ∈ ModelFund p t n e) (hB : B ∈ ModelFund p t n e) (hC : C ∈ ModelFund p t n e)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (cAB : Commutes A B) (cAC : Commutes A C) (cBC : Commutes B C) : False := by
  cases t
  ·
    simp only [FunTwoType] at ht
    rcases ht with rfl | rfl
    · exact noThree_psl4 hp2 hA hB hC hAB hAC hBC cAB cAC cBC
    · exact noThree_psl5 hp2 hA hB hC hAB hAC hBC cAB cAC cBC
  ·
    simp only [FunTwoType] at ht
    rcases ht with rfl | rfl
    · exact noThree_psu4 hp2 hadm hA hB hC hAB hAC hBC cAB cAC cBC
    · exact noThree_psu5 hp2 hadm hA hB hC hAB hAC hBC cAB cAC cBC
  ·
    simp only [FunTwoType] at ht
    subst n
    exact noThree_psp2 hp2 hadm hA hB hC hAB hAC hBC cAB cAC cBC
  ·
    simp only [FunTwoType] at ht
    subst n
    by_cases hq : 5 ≤ p ^ e
    · exact noThree_odd3 hp2 hq hadm hA hB hC hAB hAC hBC cAB cAC
    · have hodd : Odd (p ^ e) := odd_pow_of_ne_two p hp2 e
      have h2 : 2 ≤ p ^ e := by
        calc 2 ≤ p := (Fact.out : p.Prime).two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ e := Nat.pow_le_pow_right (by have := (Fact.out : p.Prime).two_le; omega) hadm.2.1
      have hpe3 : p ^ e = 3 := by
        obtain ⟨m, hm⟩ := hodd
        omega
      obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp hpe3
      exact smallNoThree3 .POmegaOdd 3 hadm
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) A hA B hB C hC hAB hAC hBC cAB cAC cBC
  ·
    simp only [FunTwoType] at ht
  ·
    simp only [FunTwoType] at ht
    subst n
    by_cases hq : 5 ≤ p ^ e
    · exact noThree_minus4 hp2 hq hadm hA hB hC hAB hAC hBC cAB cAC
    · have hodd : Odd (p ^ e) := odd_pow_of_ne_two p hp2 e
      have h2 : 2 ≤ p ^ e := by
        calc 2 ≤ p := (Fact.out : p.Prime).two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ e := Nat.pow_le_pow_right (by have := (Fact.out : p.Prime).two_le; omega) hadm.2.1
      have hpe3 : p ^ e = 3 := by
        obtain ⟨m, hm⟩ := hodd
        omega
      obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp hpe3
      exact smallNoThree3 .POmegaMinus 4 hadm
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) A hA B hB C hC hAB hAC hBC cAB cAC cBC
  ·
    exact no_three_g2d4 hp2 (Or.inl rfl) hadm hA hB hC cAB cAC cBC
  ·
    simp only [FunTwoType] at ht
  ·
    simp only [FunTwoType] at ht
  ·
    simp only [FunTwoType] at ht
  ·
    simp only [FunTwoType] at ht
  ·
    simp only [FunTwoType] at ht
  ·
    exact no_three_g2d4 hp2 (Or.inr rfl) hadm hA hB hC cAB cAC cBC
  ·
    simp only [FunTwoType] at ht
  ·
    simp only [FunTwoType] at ht
  ·
    simp only [FunTwoType] at ht
  ·
    simp only [FunTwoType] at ht

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
