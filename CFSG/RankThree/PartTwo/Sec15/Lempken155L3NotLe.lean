module

public import CFSG.RankThree.PartTwo.Sec15.Lempken155L3NotLeSplit
public import CFSG.RankThree.PartTwo.Sec15.MathAsch1513Of316
public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1Item1730Final
import CFSG.RankThree.PartTwo.Sec15.Lempken155L3NotLeMeets
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec15.Lempken155L3NotLeLeK
import CFSG.RankThree.PartTwo.Sec15.Lempken155L3NotLeO2
import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3L34
import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3Route

public section

namespace CFSG.RankThree.PartTwo.Sec15.LempkenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]


theorem res1L112InPt_l3Even_of_cover
    (h316 : Sec19.Item316)
    (hcov : Res1Omega1513.Res1CoverL3) {P : ∀ (Y : Type) [Group Y], Prop} :
    Sylow155R1.Res1L112InPt Res1L3EvenPt P := by
  intro G _ _ A c L hR hPt hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hL3, hnPGL⟩, e, he, hiso⟩ := hPt
  have hK0 : K ∈ scriptY0 A (lB A) := hC.mem_k.prop
  have hΩ : omegaA A = {Subgroup.zpowers c} :=
    Res1Omega1513.omegaA_eq_of_isoLThreePi h316 hR hiso hnPGL hN ⟨K, hK0⟩
  have h142 : Concl142 A (lB A) := Sec14.Ronan148M.concl142S14_holds G A c L hS
  have hLΔ : L ≤ delta A (lB A) L :=
    Sylow155R1.le_delta_of_lThreePi
      (Sec14.step142LowerGenL3_of_res8 (h131 := Sec13.rank3II_13_1_holds)
        (h9 := Sec14.ks142L3HessGenNine_of_model (hM := Sec14.ks142L3HessGenNineModel_proof))
        (hPGL := Sec14.step142LowerGenL3PGL_proof)) hR h142 hL3
      (GagenL3.not_z3_l34_of_scriptY0 Sec13.rank3II_13_1_holds
        (Res1Omega1513.item1513R_of_item316 h316) item1510R_holds step169TwoBridge_holds hR
        ⟨K, hK0⟩)
  have hmeet : MeetsY4 A (lB A) L K :=
    meetsY4_of_omegaA_eq (Sec16.step1513MeetsPoint_of_steps148
      Sec14.Ronan148C.step148Core_holds Sec14.Ronan148M.step148Point_holds
      Sec14.Ronan148M.step148KType_holds) hR hΩ hiso hK0
  obtain ⟨hKL, hLK⟩ := hcov G A c L hR e hiso hnPGL hN K hC.mem_k hmeet
  have hO2N : CFSG.Open.pCoreOf 2 L ≤ Subgroup.normalizer (K : Set G) :=
    Sylow155R1.pCoreOf_two_le_normalizer_of_mem_scriptY0Star hR hC.mem_k hN
      (GagenL3.item153Main_of_l3 h316 hR hL3)
      (Res1PtInputs.claim153Obs_at Sec14.Ronan148M.item148R_holds
        Sec14.Ronan149.item149S14_holds hR
        (Res1PtInputs.item152_at_lThreePi Sec14.Ronan149.item149S14_holds
          Sec14.Ronan148M.item148R_holds item134_holds Sec11.Close.closed_sec4Item4_8
          Sec4.Sporadic.rank3II_4_15 KFacts.kpSz hR hiso))
      (Sec14.item1411_1R_holds G A c L hR) h142 item135_holds
      (Sec16.Proof1613.three_dvd_card_L hR.toSec14Std)
  have hLleK : L ≤ K := le_of_eq_inf_sup_of_pCoreOf_two_le_normalizer hR hK0.1 hLK hO2N
  have hKeq : K = L ⊔ CFSG.Open.pCoreOf 2 K := by
    rw [inf_eq_right.mpr hLleK] at hKL
    exact hKL
  have hLq := Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423
    (M := Subgroup.centralizer ({c} : Set G)) hR.toSec13Data.mem_thetaComponentsAt
  have hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
    @Proof1515.theta_eq_pCore_two_of_multFree (↥L)
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) _ _ _
      (CFSG.LocalCores.isQuasisimple_nontrivial hLq)
      (item135_holds G A c L hR.toSec13Data hR.hypS_or_hypT) ⟨MulEquiv.refl _⟩
      (Proof1515.multFree_of_isLThreePi hL3)
  exact ⟨hLΔ, hLleK, hKeq,
    l3_pCoreOf_le_of_ctx155 (item154R_of_item159R (item159R_of_h316 h316)) hR hΩ he hC hLleK
      hKeq (isoLThreePi_quot_pCore_two_of_cover hLleK hKeq hθ hiso)⟩

end CFSG.RankThree.PartTwo.Sec15.LempkenL3
