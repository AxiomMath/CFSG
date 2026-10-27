module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofA7
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsHJ
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1515LA7L325 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → omegaA A = {Subgroup.zpowers c} →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y →
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) →
      ∀ _ : Fact (Nat.Prime 5), IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))

@[expose] noncomputable def Step1515LA7Y0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → omegaA A = {Subgroup.zpowers c} →
    (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSU 3 5 1)) →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y →
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) →
      ∀ Y₀ ∈ scriptY0Star A (lB A), Y₀ ≠ Y → ¬ L ≤ Y₀

@[expose] noncomputable def Step1515LA7Simple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → omegaA A = {Subgroup.zpowers c} →
    (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSU 3 5 1)) →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y →
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) →
      (∀ Y₀ ∈ scriptY0Star A (lB A), ¬ L ≤ Y₀) →
        IsSimpleGroup ↥L ∧
          Odd (Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓
            Subgroup.centralizer (L : Set G)))

namespace Proof1515

theorem card_projSU_three_five [Fact (Nat.Prime 5)] :
    Nat.card (CFSG.Assembly.RankThreeEven.projSU 3 5 1) = 126000 :=
  CFSG.PGLModel.card_projSU_three_five

end Proof1515

open Proof1515


theorem step1515LA7_of (h148 : Item148R) (hbot : Item145BotS14) (hL325 : Step1515LA7L325)
    (hY0 : Step1515LA7Y0) (hsimp : Step1515LA7Simple) : Step1515LA7 := by
  intro G _ _ A c L h p e _ he hiso hΩ Y hY hm hYL hY7
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hYΔ := eq_deltaZero_of_mem_scriptY4 hbot h hY4
  obtain ⟨φY⟩ := hY7
  have hYc : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 2520 := by
    rw [Nat.card_congr φY.toEquiv, card_alternatingGroup_seven]
  have hQs : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    Proof1514.isSimpleGroup_of_mulEquiv_alternating (by norm_num) φY
  have heq : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
    pPrimeCore_three_eq_pCore_two (pPrimeCore_three_eq_bot_of_isSimpleGroup hQs
      (by rw [hYc]; norm_num))
  have hY7' : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 2520 := by
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq heq).toEquiv, hYc]
  have h3L : 3 ∣ Nat.card L :=
    (Proof1514.three_dvd_card_inf_of_meetsY4 hm).trans (Subgroup.card_dvd_of_le inf_le_left)
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      L' = L := by
    intro c' L' hc' hL'
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact hc'
    exact eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hcc hL'
  have hU : ∃ _ : Fact (Nat.Prime 5), Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSU 3 5 1) := by
    rcases cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hY4 hYΔ with
      ⟨c', hc', -, L', hL', hcases⟩ | ⟨c', L', hc', hL', ⟨φJ⟩, -⟩ |
        ⟨⟨φ10⟩, -, -⟩ | ⟨c', L', n, m, hc', hL', -, -, hiso', -⟩
    · obtain rfl := hpt c' L' hc' hL'
      rcases hcases with hφ | ⟨hL'', -⟩ | ⟨p', f, e', hp', -, -, -, hε⟩ | ⟨⟨φJ⟩, -⟩
      · exfalso
        obtain ⟨φ⟩ := hφ
        exact Proof1514.not_isoLThreePi_of_card_2520 (by
          rw [← Nat.card_congr φ.toEquiv, hY7']) p e hiso
      · rcases hL'' with hM | ⟨_, ⟨φ⟩⟩ | hU
        · obtain ⟨φM⟩ := hM
          exact (KFacts.KS14.not_isoLThreePi_M22 p e (isoLThreePi_congr φM hiso)).elim
        · exact ((hL325 G A c L' h hΩ Y hY hm hYL ⟨φY⟩ inferInstance).false φ).elim
        · exact hU
      · exact (not_isLThreeEpsAt_of_card_2520 hY7' p' f hε).elim
      · exact (Proof1514.not_isoLThreePi_of_j2 φJ hiso).elim
    · obtain rfl := hpt c' L' hc' hL'
      exact (Proof1514.not_isoLThreePi_of_j2 φJ hiso).elim
    · exfalso
      have h1 := Nat.card_congr φ10.toEquiv
      rw [hY7', KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2] at h1
      omega
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact Proof1514.not_isoLThreePi_of_card_2520 hY7' 2 (3 * n) hiso'
  obtain ⟨_, ⟨φU⟩⟩ := hU
  have hnotY : ¬ L ≤ Y := by
    intro hLY
    have hdvd := Proof1514.card_thetaQuot_dvd hLY
    rw [Nat.card_congr φU.toEquiv, card_projSU_three_five, hYc] at hdvd
    exact absurd hdvd (by norm_num)
  have hno : ∀ Y₀ ∈ scriptY0Star A (lB A), ¬ L ≤ Y₀ := by
    intro Y₀ hY₀
    by_cases hYY : Y₀ = Y
    · rw [hYY]
      exact hnotY
    · exact hY0 G A c L h hΩ ⟨inferInstance, ⟨φU⟩⟩ Y hY hm hYL ⟨φY⟩ Y₀ hY₀ hYY
  obtain ⟨hs, hodd⟩ := hsimp G A c L h hΩ ⟨inferInstance, ⟨φU⟩⟩ Y hY hm hYL ⟨φY⟩ hno
  exact ⟨⟨inferInstance, ⟨φU⟩⟩, hno, hs, hodd⟩

end CFSG.RankThree.PartTwo.Sec15
