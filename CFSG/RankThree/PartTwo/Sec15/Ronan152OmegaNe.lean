module

public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25Cases
public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixL1
public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixConj
public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixEnd
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofS17
import CFSG.RankThree.PartTwo.Sec15.Item155wProofHJ
import CFSG.RankThree.PartTwo.Sec15.Item15Res10ProofV
import CFSG.RankThree.PartTwo.Sec16.Item162Proof
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step152SL25OmegaNeR_of_big
    (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    (hbot : Item145BotS14) (hloc : Claim1411LocalR) (h152 : Item152BigR)
    (h153 : Item153MainJ2R) (h155 : Item155wJ2R) : Step152SL25OmegaNeR := by
  intro G _ _ A c L hR _ M X hctx B b d Lb hB hc hcent hΩne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := hR.isE27
  obtain ⟨hbΩ, hLb, hJ, -, -, -, hdA, hd1, hdc, -⟩ := Ronan152SL25.lbConfig_facts hA hB hc
  have hRb : Sec15R G A b Lb := Sec16.sec15R_of_point hR hbΩ hLb
  have hSb := hRb.toSec14Std
  have hDb := hRb.toSec13Data
  have hcent' : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (Subgroup.closure {b, d} : Set G) := by
    rw [hcent, hc.1]
  have hfix := Ronan152Six.pCoreOf_inf_centralizer_ne_bot h142 hSb hJ hctx hdA hd1 hdc hcent'
  have hdZ : IsZCentral Lb d := by
    have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
    obtain ⟨hdL, S, hS1, hS2⟩ := hdc
    obtain ⟨-, -, hθ3, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
    obtain ⟨hSy, hZ⟩ := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hS1 hS2
    exact ⟨_, hSy, hZ⟩
  have hO2 : CFSG.Open.pCoreOf 2 Lb ≠ ⊥ := fun h0 => hfix (by rw [h0, bot_inf_eq])
  have hLbtop : Lb ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one hRb.toTheoremFourHyp
    hDb.ne_one (top_le_iff.mp (htop ▸ hDb.le_centralizer))
  have hperf := Sec6.isPerfect_of_mem_thetaComponentsAt hDb.mem_thetaComponentsAt
  obtain ⟨eθ⟩ := hJ
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hsimp : IsSimpleGroup (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) := eθ.isSimpleGroup
  have h3L : 3 ∣ Nat.card Lb := three_dvd_card_of_thetaQuot_j2 ⟨eθ⟩
  obtain ⟨eJ⟩ := Sec12.gap128OTwoHJ ↥Lb (hRb.toTheoremFourHyp.sectionFourHyp hLbtop) hperf ⟨eθ⟩
  have hq : CFSG.IsQuasisimple (↥Lb ⧸ CFSG.pCore 2 ↥Lb) :=
    isQuasisimple_of_mulEquiv_nativeJ2 CFSG.Sporadic.J2.isSimpleGroup_J2
      (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15) eJ
  have hLb4 : Lb ∈ scriptY4 A (lB A) :=
    ⟨⟨hLbtop, hDb.le_normalizer⟩, Sec16.eq_oPrimeResidualOf_of_isSimpleGroup hperf hsimp h3L,
      le_antisymm (Proof155w.le_delta_of_le_of_j2 hSb ⟨eθ⟩ le_rfl) (delta_le Lb), hq⟩
  have hLb0 : Lb ∈ scriptY0 A (lB A) := ⟨hLb4, ⟨hLbtop, hDb.le_normalizer⟩, hO2⟩
  obtain ⟨Y₀, hLbY₀, hY₀⟩ := (Set.toFinite (scriptY0 A (lB A))).exists_le_maximal hLb0
  have hLJ : Nat.card (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) = 604800 := by
    rw [Nat.card_congr eθ.toEquiv, KFacts.KS14.card_nativeJ2]
  have hdvd : 604800 ∣ Nat.card (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := hLJ ▸ Proof1514.card_thetaQuot_dvd hLbY₀
  obtain ⟨hYeq, hLeq⟩ : Y₀ = (Y₀ ⊓ Lb) ⊔ CFSG.Open.pCoreOf 2 Y₀ ∧
      Lb = (Lb ⊓ Y₀) ⊔ CFSG.Open.pCoreOf 2 Lb := by
    rcases step1515HJListLe_of h148 hbot h134 h48 G A b Lb hRb ⟨eθ⟩ Y₀ hY₀ hLbY₀ with
      h5 | h36 | hON | hfac
    · obtain ⟨e5⟩ := h5
      rw [Nat.card_congr e5.toEquiv, card_alternatingGroup_five] at hdvd
      norm_num at hdvd
    · rw [card_of_isTripleCover h36, card_alternatingGroup_six] at hdvd
      norm_num at hdvd
    · rw [card_of_isTripleCover hON, CFSG.Sporadic.ON.card_ON_eq] at hdvd
      norm_num at hdvd
    · exact hfac
  have hm : MeetsY4 A (lB A) Lb Y₀ := ⟨Lb, hLb4, le_inf le_rfl hLbY₀⟩
  have hconf : Conf1515HJ A b Lb Y₀ := ⟨hRb, ⟨eθ⟩, hY₀, hm, hYeq, hLeq, hΩne⟩
  have hV : Step1515HJV := step1515HJV_of_tail
    (step1515HJD_of_res4 h134 h48 (step1515HJConj_of_big h152 h153 h155)
      (step1515HJQN_of_big h152 h153 h155) hloc) step1515HJVTail_of_res10
  have hO2c := hV G A b Lb hRb ⟨eθ⟩ Y₀ hY₀ hm hYeq hLeq hΩne
  have hYc : Y₀ ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [hYeq]
    exact sup_le (inf_le_right.trans hDb.le_centralizer) hO2c
  exact hconf.false_of_le_centralizer_big (step1515HJTrans_of h134 h48) (h152 G A b Lb hRb)
    (h153 G A b Lb hRb) (h155 G A b Lb hRb) hYc hdA hd1 hdZ hfix

theorem y4CoreExclSL25HJR_of_oneOmega_big
    (h1 : Step152SL25OneOmegaR) (h142 : Item142AllS14) (h425 : Sec4.Item4_25Fix)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h41 : Sec4.Item4_1LargePrime)
    (hGW : Sec6.GWLBalanceStatement) (h148 : Item148R) (hbot : Item145BotS14)
    (hloc : Claim1411LocalR) (h152 : Item152BigR) (h153 : Item153MainJ2R)
    (h155 : Item155wJ2R) : Y4CoreExclSL25HJR :=
  y4CoreExclSL25HJR_of_omega h142 h425 h134 h48 h41 hGW h1
    (step152SL25OmegaNeR_of_big h142 h134 h48 h148 hbot hloc h152 h153 h155)

end CFSG.RankThree.PartTwo.Sec15
