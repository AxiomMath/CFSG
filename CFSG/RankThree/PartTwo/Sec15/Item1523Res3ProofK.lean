module

public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofDefs
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofCover
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsHJ
import CFSG.RankThree.PartTwo.Sec16.Item162Proof
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofON
public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step1523KReadY4_of_type
    (h148 : Item148R)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142R) (h156 : Item156R)
    (h1514 : Item1514HJR) (hT : Step1523KTypeY4) : Step1523KReadY4 := by
  intro G _ _ A c L h hJ Y hY hm
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hYΔ := Proof1523Res3.eq_deltaZero_of_mem_scriptY4 h134 h48 h hY4
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY4
  have hJc : Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800 := KFacts.KS14.card_nativeJ2
  have h3J : 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
    rw [hJc]
    norm_num
  have h156Y := h156 G A c L h Y hY
  rcases Proof1523Res3.cases148Full_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hY4 hYΔ
    with ⟨c', hc', hdec, L', hL', hcases⟩ | ⟨c₃, d, L₃, hc₃, hL₃, hJ₃, hdA, hd1, hdc, hdec₃, h3⟩ |
      ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, -⟩ | ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
  ·
    exfalso
    obtain ⟨φJ'⟩ := Proof1523Res3.lA_j2_of_j2 h134 h48 h hJ hc' hL'
    rcases hcases with hφ | ⟨hL'', -⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨-, h6 | h5⟩
    ·
      obtain ⟨φ⟩ := hφ
      have h' := Sec16.sec15R_of_point h hc' hL'
      have hO := Proof1515.pPrimeCore_eq_pCore_of_mem_scriptY4 hY4 ⟨φ.trans φJ'⟩
        Proof1515.multFree_J2
      have h3L' : 3 ∣ Nat.card L' := Proof1515.three_dvd_card_of_mulEquiv φJ' h3J
      have hnot34 : IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
        refine ⟨fun ψ => ?_⟩
        have h1 := Nat.card_congr (φJ'.symm.trans ψ).toEquiv
        rw [hJc, KFacts.KS14.card_projSL_three_four] at h1
        omega
      have hfac := Proof1515.eq_inf_sup_pPrimeCoreOf_of_item142 h' (h142 G A c' L' h') h3L'
        hnot34 hY4 hdec
      rw [Proof1515.pPrimeCoreOf_eq_pCoreOf_two hO] at hfac
      exact Proof1523Res3.not_meetsY4_of_lA h134 h48 h1514 h hJ hY hm hc' hL'
        (Proof1515Res.meetsY4_of_cover (concl142_of_j2 h134 h48 h.toSec14Std hJ) hc'
          (le_centralizer_of_mem_thetaComponentsAt hL'.1) hL'.2.1 hY4 hfac)
    ·
      rcases hL'' with hM | ⟨_, hφ⟩ | ⟨_, hφ⟩
      · obtain ⟨φM⟩ := hM
        have h1 := Nat.card_congr (φJ'.symm.trans φM).toEquiv
        rw [hJc, KFacts.KS14.card_nativeM22] at h1
        norm_num at h1
      · obtain ⟨φ⟩ := hφ
        exact Proof1514.not_isoLThreePi_of_j2 φJ' (p := 5) (e := 2)
          (Or.inl ⟨by norm_num, ⟨φ⟩⟩)
      · obtain ⟨φ⟩ := hφ
        exact Proof1514.not_isoLThreePi_of_j2 φJ' (p := 5) (e := 1)
          (Or.inr ⟨by norm_num, ⟨φ⟩⟩)
    ·
      exact Proof1514.not_isoLThreePi_of_j2 φJ' hiso
    ·
      have hc : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 1080 := by
        rw [card_of_isTripleCover h6, card_alternatingGroup_six]
      have heq := Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hY4.2.2.2 hne
        fun p hp hp6 => hc ▸ Proof1515.not_sq_dvd_small (Or.inr rfl) hp hp6
      exact h156Y.2.1 (Proof1515.isTripleCover_congr (QuotientGroup.quotientMulEquivOfEq heq) h6)
    ·
      obtain ⟨φ⟩ := h5
      have hc : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 60 := by
        rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five]
      have heq := Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hY4.2.2.2 hne
        fun p hp hp6 => hc ▸ Proof1515.not_sq_dvd_small (Or.inl rfl) hp hp6
      exact h156Y.1.false ((QuotientGroup.quotientMulEquivOfEq heq).symm.trans φ)
  ·
    obtain ⟨hO, htype⟩ : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y ∧
        ((∃ _ : Fact (Nat.Prime 7), Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃*
            CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∨
          Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))) := by
      rcases h3 with hON | hφ | ⟨h7, hφ⟩
      · exfalso
        have heq := Proof1515.pPrimeCore_three_eq_pCore_two_of hY4.2.2.2 hne
          fun Z _ hZc hcop ⟨φ⟩ => ks1515ONMult _ Z hY4.2.2.2.1 hZc hcop
            (Proof1515.isTripleCover_congr φ.symm hON)
        exact h156Y.2.2 (Proof1515.isTripleCover_congr (QuotientGroup.quotientMulEquivOfEq heq)
          hON)
      · exact ⟨Proof1515.pPrimeCore_eq_pCore_of_mem_scriptY4 hY4 hφ
          Proof1515.multFree_alternatingGroup_seven,
          Or.inr (Proof1515.nonempty_quot_pCore_two_equiv_of_multFree hY4 hφ
            Proof1515.multFree_alternatingGroup_seven)⟩
      · have hL3 : IsLThreePi (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
          ⟨7, 1, inferInstance, le_rfl, Or.inl ⟨by norm_num, ⟨MulEquiv.refl _⟩⟩⟩
        exact ⟨Proof1515.pPrimeCore_eq_pCore_of_mem_scriptY4 hY4 hφ
          (Proof1515.multFree_of_isLThreePi hL3),
          Or.inl ⟨h7, Proof1515.nonempty_quot_pCore_two_equiv_of_multFree hY4 hφ
            (Proof1515.multFree_of_isLThreePi hL3)⟩⟩
    have h₃ := Sec16.sec15R_of_point h hc₃ hL₃
    have hm₃ := Proof1523Res3.not_meetsY4_of_lA h134 h48 h1514 h hJ hY hm hc₃ hL₃
    have hdΩ := Proof1523Res3.zpowers_not_mem_omegaA_of_j2 h134 h48 h₃.toSec14Std hJ₃ hdA hd1
      hdc
    have hYK := Proof1523Res3.eq_inf_k_sup_of_dec hY4 hYΔ
      (Proof1515.pPrimeCoreOf_eq_pCoreOf_two hO) hdec₃
    obtain ⟨hK4, hKt⟩ := hT G A c₃ L₃ h₃ hJ₃ Y hY hm₃ htype d hdA hd1 hdc hdΩ hdec₃ hYK
    exact ⟨d, hdA, hd1, Proof1523Res3.isThreeCentralIn_of_onType h134 h48 h hJ hc₃ hL₃ hdA hd1
      hdc hKt, hdΩ, hK4, hKt, hYK, htype⟩
  ·
    exfalso
    have h1 := Proof1523Res3.card_lA_of_j2 h134 h48 h hJ hc' hL'
    rw [Nat.card_congr φ7.toEquiv, card_alternatingGroup_seven] at h1
    norm_num at h1
  ·
    exact (Proof1515.not_isLThreeEpsAt_of_card_j2
      (Proof1523Res3.card_lA_of_j2 h134 h48 h hJ hc' hL') 2 (n * m) hε).elim

end CFSG.RankThree.PartTwo.Sec15
