module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.S2112CasesThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217RJ1U
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1Main
public import CFSG.LocalAnalysis.UniquenessCase.UCK461Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Alpha
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899E3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.S2117PowThree
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC22S216
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsSixteen
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229KThin
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Sp4
public import CFSG.LocalAnalysis.UniquenessCase.UC22Q35NormSylowAlphaHolds
public import CFSG.Adapters.CatalogAgree
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC22Q35PermFiveHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107OutSetup
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847O3
public import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rTorus
public import CFSG.LocalAnalysis.UniquenessCase.UC22S219Three
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporRest

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem pRank_seven_le_two_dataOfSetup (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (S : Setup G) (h7σ : 7 ∉ (PartTwo.Three.dataOfSetup hS S).sig) :
    CFSG.Open.pRank 7 (PartTwo.Three.dataOfSetup hS S).M ≤ 2 :=
  Nat.le_of_not_lt fun h73 => h7σ (PartTwo.Three.mem_sigmaOf_of_three_le_pRank hS hUC
    S.witness.maxLocal (by norm_num) le_rfl h73)

theorem s21_16_17_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    (hK : F10.K105SporRest) (hK332 : UCK.K332Cyc)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSQ : PartOne.Section7.StronglyEmbeddedSolvableQ)
    (hSE5 : PartOne.Section7.StronglyEmbeddedFive)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree)
    (hSg : UC6S846.SigmaStd (PartTwo.Three.dataOfSetup hS S))
    (h614 : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S))
    (h76 : F07.R76Sig (PartTwo.Three.dataOfSetup hS S))
    (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h869N : F08.R869N (PartTwo.Three.dataOfSetup hS S))
    (h207 : S20_7 (PartTwo.Three.dataOfSetup hS S))
    (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True))
    (hn3 : H1930 (PartTwo.Three.dataOfSetup hS S) →
      ∀ c : Ctx21 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True), 3 ≤ c.n)
    (h5 : S21_5 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True))
    (h3 : S21_3 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True))
    (hKF7 : KF7Use (PartTwo.Three.dataOfSetup hS S))
    (h14 : S21_14 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True))
    (hL3PTwo : S21_12aFR34L3PTwo (PartTwo.Three.dataOfSetup hS S)
      (Choice214U (PartTwo.Three.dataOfSetup hS S)))
    (hEv2 : S21_12aFR34F2Even2 (PartTwo.Three.dataOfSetup hS S)
      (Choice214U (PartTwo.Three.dataOfSetup hS S))) :
    S21_16 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) ∧
      S21_17 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) ∧
      F08.R8107 (PartTwo.Three.dataOfSetup hS S) := by
  let D := PartTwo.Three.dataOfSetup hS S
  let T : Choice2011 G := fun _ _ => True
  change S21_16 D T ∧ S21_17 D T ∧ F08.R8107 D
  have h15T := s21_15Two_of_certificate113 D T h211 hSg (uc22r899e3_dataOfSetup hS hUC S)
  have h6 := s21_6Inf_of_k105Spor h3 h5 hn3 (F10.k105Spor_of_rest hK) (by
    intro X _ _ _ s hs ⟨e⟩
    exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor.two_le_pRank_three_sporadic_ne_J1
      hs ⟨e.trans (CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s).some⟩) (by
    intro X _ _ hsimp hnc s ⟨e⟩
    exact CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds X hsimp hnc s
      ⟨e.trans (CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s).some⟩)
  have h8107 : F08.R8107 D :=
    R8107Out.r8107_dataOfSetup hSE5 KBridge.kThinSimple_holds hS S hSg h82
      (R847O3.r847OrderThree_dataOfSetup hSE5 PartOne.Section7.stronglyEmbeddedFiveZ_holds
        KBridge.kThinSimple_holds hS S hSg) h76 h614
  have hEv := s21_12aFR34F2Even_of_f2Even2 kFieldAutOdd_holds kFunSplit_holds kFunCount_holds
    hGA hSg hKF7 hn3 h5 h82 h211 (fun _ _ _ => trivial) hEv2
  have hF2 := s21_12aFR34F2_of_sig_even kFieldAutOdd_holds kFunSplit_holds kFunCount_holds
    kq35NormSylowAlpha_holds kQ35PermFive_holds hGA hSg hKF7 hn3 h5 h82 h211
    (fun _ _ _ => trivial) (s21_12aFR34F2Sig_dataOfSetup hS hUC S) hEv
  have h212 := s21_12_dataOfSetup_of_l3PTwo_f2 hS hUC hC S h82 h207 h211 h3 h614 hL3PTwo hF2 T
  have h920J1 := PartOne.Section9.r920J1_dataOfSetup hSQ hSE5 hSE3 hK332 UCK.k32_holds
    UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds hS S h82 h614
  have h17J := s21_17RJ1_of_three D T h211 h5 hn3 h6 hSg h8107 h920J1
    (pRank_seven_le_two_dataOfSetup hS hUC S)
  have h17RT := s21_17RT_of_s21_17RT2 h212 h869N hn3
    (s21_17RT2_of_s21_17RJ1 hS.rank hSE3 h82 hn3 h17J)
  have h16 := s21_16_of_s21_6Inf h6 h212 (s21_13_of h3 h5 hn3) h14
    CFSG.Open.QTFaithfulEmptyTauCeti.catalogAgree
  have h17 := s21_17_of_residualT hS.rank hGA h211
    (PartTwo.Three.s21_17R_one_pow_of_three hS.rank hGA D T) hSg
    (conclusion76_of_r76Sig h76) h16 h15T (s21_normalSp4_of D T hSg h211) h17RT
  exact ⟨h16, h17, h8107⟩
