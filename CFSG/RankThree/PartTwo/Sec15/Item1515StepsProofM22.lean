module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofFactor
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open Proof1515


theorem step1515M22_of (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R) :
    Step1515M22 := by
  intro G _ _ A c L h hL22 hΩ Y hY _
  obtain ⟨φL⟩ := hL22
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hYΔ := eq_deltaZero_of_mem_scriptY4 hbot h hY4
  have hL443 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 443520 := by
    rw [Nat.card_congr φL.toEquiv, KFacts.KS14.card_nativeM22]
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_mulEquiv φL (by rw [KFacts.KS14.card_nativeM22]; norm_num)
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Subgroup.zpowers c' = Subgroup.zpowers c ∧ L' = L := by
    intro c' L' hc' hL'
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact hc'
    exact ⟨hcc, eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hcc hL'⟩
  have hnot34 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
    refine ⟨fun ψ => ?_⟩
    have h1 := Nat.card_congr ψ.toEquiv
    rw [hL443, KFacts.KS14.card_projSL_three_four] at h1
    omega
  rcases cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hY4 hYΔ with
    ⟨c', hc', hdec, L', hL', hcases⟩ | ⟨c', L', hc', hL', ⟨φJ⟩, -⟩ |
      ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, -⟩ | ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
  · obtain ⟨hcc, rfl⟩ := hpt c' L' hc' hL'
    have hO : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y := by
      rcases hcases with hφ | ⟨-, h7⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨hJ, -⟩
      · obtain ⟨φ⟩ := hφ
        exact pPrimeCore_eq_pCore_of_mem_scriptY4 hY4 ⟨φ.trans φL⟩ multFree_M22
      · exact pPrimeCore_eq_pCore_of_mem_scriptY4 hY4 h7 multFree_alternatingGroup_seven
      · exact (KFacts.KS14.not_isoLThreePi_M22 p (f * e) (isoLThreePi_congr φL hiso)).elim
      · obtain ⟨φJ⟩ := hJ
        rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at hL443
        omega
    rw [hcc] at hdec
    have hfac := eq_inf_sup_pPrimeCoreOf_of_item142 h (h142 G A c L' h) h3L hnot34 hY4 hdec
    rw [pPrimeCoreOf_eq_pCoreOf_two hO, inf_comm] at hfac
    exact hfac
  · obtain ⟨-, rfl⟩ := hpt c' L' hc' hL'
    rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at hL443
    omega
  · obtain ⟨-, rfl⟩ := hpt c' L' hc' hL'
    rw [Nat.card_congr φ7.toEquiv, card_alternatingGroup_seven] at hL443
    omega
  · obtain ⟨-, rfl⟩ := hpt c' L' hc' hL'
    exact (KFacts.KS14.not_isLThreeEpsAt_M22 2 (n * m) (IsLThreeEpsAt.of_mulEquiv φL hε)).elim

end CFSG.RankThree.PartTwo.Sec15
