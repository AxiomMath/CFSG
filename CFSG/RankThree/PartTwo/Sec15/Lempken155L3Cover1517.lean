module

public import CFSG.RankThree.PartTwo.Sec15.Lempken155L3CoverPt
public import CFSG.RankThree.PartTwo.Sec15.Item15Res9ProofTL
public import CFSG.RankThree.PartTwo.Sec15.KL3Sub2ProofNorm
public import CFSG.RankThree.PartTwo.Sec15.KL3FactsProofHess
public import CFSG.RankThree.PartTwo.Sec15.Item15Res9ProofY0

public section

namespace CFSG.RankThree.PartTwo.Sec15.Res1Cover

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec15.Proof15Res6
  CFSG.RankThree.PartTwo.Sec15.Proof1513Steps
open Proof1517

variable {G : Type} [Group G] [Finite G]

section Item135


theorem item135Simple_holds : Item135Simple :=
  Sec13.item135Simple_narrow (Sec13.item4_4Types135_of_item4_4
      Sec4.Census.rank3II_4_4_of_griess_noItem41)
    (Sec13.ks135TwoRank_of_cover Sec13.ks135TwoRankCover Sec4.Sporadic.rank3II_4_14_local
      Sec4.Sporadic.rank3II_4_15)
    KFacts.KS14.sporadicModels131 Sec4.Sporadic.rank3II_4_14_local Sec4.Sporadic.rank3II_4_15
    Sec13.item135SimpleL3

end Item135


theorem step1516R_of_item316
    (h316 : Sec19.Item316) : Step1516R := by
  intro G _ _ A c L h Y hctx
  exact rank3II_15_16_of h (item153Main_of_ctx1514 h316 h hctx)
    (claim153Obs_of_ctx1514 h hctx) (Ronan149.item149S14_holds G A c L h.toSec14Std)
    (Sec14.item1411_1R_holds G A c L h) (Sec14.claim1411LocalR_holds G A c L h) Y hctx

theorem step1517Y0_holds
    : Step1517Y0 := by
  intro G _ _ A c L h Y hctx X hX hLX
  have h152 : Item152 A (lB A) := item152_of_ctx1514 h hctx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL4 := mem_scriptY4_L item135Simple_holds
    (Sec14.concl142R_of_S14 Ronan148M.concl142S14_holds) item1510R_holds
    step169TwoBridge_holds Ronan138S.item138N_holds
    (ks1517Gen_of (ks1517CentGen_of Sec14.ks1517SeitzU)) h hctx
  set M := Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) with hM
  have hM2 : M ∈ scriptY2 A :=
    Sec16.normalizer_pCoreOf_mem_scriptY2 h.isSimpleGroup h.nonabelian hX
  have hLM : L ≤ M := hLX.trans (Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hX.2
  have hF : generalizedFitting ↥M = CFSG.pCore 2 ↥M :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥M 2).mp
      (CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal h.toTheoremFourHyp.charTwoType hloc)
  obtain ⟨J, -, hLJ, hJ0⟩ := h152 L hL4 M hM2 hLM hF
  obtain ⟨Y₀, hJY₀, hY₀⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hJ0
  exact ⟨Y₀, hY₀, hLJ.trans hJY₀⟩

theorem step1517Con_of_item316
    (h316 : Sec19.Item316) : Step1517Con := by
  intro G _ _ A c L h Y hctx Y₀ hY₀ _ hLY₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀, hS₀Y₀⟩ :=
    Sec16.exists_qStar_le_normalizer (item153Main_of_ctx1514 h316 h hctx)
      (claim153Obs_of_ctx1514 h hctx) hY₀
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hOQ : O ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨step1517Q0_of Ronan149.item1444S14_holds Proof148FourK.item146S14_holds
        Ronan149.item145BotS14_holds Ronan148M.concl142S14_holds G A c L h Y hctx, le_top⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two O).mpr hO2⟩
  obtain ⟨w, hw, hOw⟩ := Sec16.exists_conj_le_normalizer
    (Sec14.item1411_1R_holds G A c L h) hS₀ hS₀Y₀ hOQ
  set Y₁ := Y₀.map (MulAut.conj w).toMonoidHom with hY₁def
  have hY₁ : Y₁ ∈ scriptY0Star A (lB A) := Sec16.map_conj_mem_scriptY0Star hw hY₀
  obtain ⟨-, -, -, -, -, -, hYL, -, hΩ⟩ := hctx.concl1515
  obtain ⟨-, h9, -⟩ := Proof1517.point_facts h hctx
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
  have hYY₁ : Y ≤ Y₁ :=
    le_of_le_normalizer_of_cover hctx.mem_y0Star.prop.1.2.1 hYL hLY₁ hYN
  have hYeq : Y = Y₁ := hctx.mem_y0Star.eq_of_le hY₁.prop hYY₁
  exact hctx.not_le (hYeq ▸ hLY₁)

theorem step1517R_of_item316
    (h316 : Sec19.Item316) : Step1517R :=
  step1517R_of step1517Y0_holds (step1517Con_of_item316 h316)
    (step1517Simple_of item135Simple_holds)

theorem step1518R_of_item316
    (h316 : Sec19.Item316) : Step1518R :=
  step1518R_of_norm (step1516R_of_item316 h316) (step1517R_of_item316 h316)
    (step1518TL_of (Sec14.item142R_of_wired item142AllS14_holds)
      Ronan138S.item138N_holds)
    KL3Sub2Proof.ks1518Norm

theorem step1519R_of_item316
    (h316 : Sec19.Item316) : Step1519R :=
  step1519R_of_named (step1518R_of_item316 h316) (step1517R_of_item316 h316)
    item135Simple_holds
    (Sec14.concl142R_of_S14 Ronan148M.concl142S14_holds) item1510R_holds
    step169TwoBridge_holds Ronan138S.item138N_holds
    (step1519CentAut_of_y0E9'
      (step1519Y0E9_of (Res1H1.item1511R_of_item316 h316)
        (Sec16.step1513MeetsPoint_of_steps148 Ronan148C.step148Core_holds
          Ronan148M.step148Point_holds Ronan148M.step148KType_holds)
        Ronan148M.item148R_holds Ronan149.item145BotS14_holds Ronan138S.item138N_holds))

end CFSG.RankThree.PartTwo.Sec15.Res1Cover
