module

public import Certificates.Certificate291400
public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps87Four
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4Holds
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporRestEHolds
public import Certificates.Certificate9726
public import Certificates.Certificate17430
public import Certificates.Certificate431004
public import CFSG.LocalAnalysis.UniquenessCase.UC22Main74
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporRest
public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps79
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListSporA
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicCoverCenterOddHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22K108HCore
import CFSG.LocalAnalysis.UniquenessCase.UC22K108Holds
import CFSG.LocalAnalysis.UniquenessCase.UC22K331Holds
import CFSG.LocalAnalysis.UniquenessCase.UC22K331Residue
import CFSG.LocalAnalysis.UniquenessCase.UC22S206x
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Setup4
import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7UseFour
import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadNoStrongHolds
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps80
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229KThin
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C5Res
import CFSG.LocalAnalysis.UniquenessCase.UC22S215Setup4
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UC6R77Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps81
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332RowsRest
public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps87
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporRestE
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanTorusU7
import CFSG.LocalAnalysis.UniquenessCase.UC6K332RowsHolds
import CFSG.LocalAnalysis.UniquenessCase.UCK35wHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.GolayEven
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ModFacts
public import CFSG.Monster.B.TwoA.Sp8.P0RankSound
public import CFSG.Quasithin.H13.KGFactT3J4Core
public import Certificates.Certificate10506
public import Certificates.Certificate10507
public import Certificates.Certificate10508
public import Certificates.Certificate10510
public import Certificates.Certificate10511
public import Certificates.Certificate24531
public import Certificates.Certificate24550
public import Certificates.Certificate812201
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallAutFix
import CFSG.LocalAnalysis.UniquenessCase.UC22S206s
import CFSG.Quasithin.Background.H12OneHatM22
import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M22
import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case2


public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

open CFSG.Yardstones.Mf4cdcdf2e013 (Theorem2219Four)



theorem theorem2219Four_of_setup_frontier




















    (hKA : KLieBorelAutPrime) : Theorem2219Four := by
  have h : ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G)
      (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G), S.InMSigma → PartIAt S.M →
        Steps87 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
    fun _ _ _ hS hU S hMS hPart => steps87_dataOfSetup4 hS hU S hMS hPart
  have steps81 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G)
      (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G), S.InMSigma → PartIAt S.M →
        Steps81 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) := by
    have hgr := CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
    have hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
        s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      intro X _ _ _ s hs ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor.two_le_pRank_three_sporadic_ne_J1
        hs ⟨e.trans b⟩
    have hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
        ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2 := by
      intro X _ _ hsimp hnc s ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds X hsimp hnc s
        ⟨e.trans b⟩
    have hord : ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName),
        (s = .M11 ∨ s = .M22 ∨ s = .M23 ∨ s = .HS) → IsSpor X s → ¬ 27 ∣ Nat.card X := by
      intro X _ _ s hs ⟨e⟩
      rw [Nat.card_congr e.toEquiv]
      rcases hs with rfl | rfl | rfl | rfl
      · rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) = 7920 from
          CFSG.Sporadic.Mathieu.card_M11]
        decide
      · rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 from
          CFSG.Sporadic.Mathieu.card_M22]
        decide
      · rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M23) = 10200960 from
          CFSG.Sporadic.Schreier.m23_card]
        decide
      · rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .HS) = 44352000 from
          CFSG.Sporadic.HS.card_HS]
        decide
    have hJHe : ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName),
        (s = .J2 ∨ s = .He) → IsSpor X s → 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) ∧
          ¬ 125 ∣ Nat.card X ∧ 3600 < Nat.card X := by
      intro X _ _ s hs ⟨e⟩
      have : Finite (CFSG.Blueprint.NativeSporadic.Carrier s) := Finite.of_equiv X e.toEquiv
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) e,
        Nat.card_congr e.toEquiv]
      rcases hs with rfl | rfl
      · obtain ⟨x, y, -, hx, hy, hxy, hc, -⟩ := CFSG.SectionRank.J2_sylow5_square_witness
        refine ⟨CFSG.SectionRank.QTK.two_le_pRank_of_square Nat.prime_five hx hy hxy hc, ?_⟩
        rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J2) = 604800 from
          CFSG.Sporadic.J2.card_J2]
        decide
      · obtain ⟨x, y, -, hx, hy, hxy, hc, -⟩ := CFSG.SectionRank.He_sylow5_square_witness
        refine ⟨CFSG.SectionRank.QTK.two_le_pRank_of_square Nat.prime_five hx hy hxy hc, ?_⟩
        rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) = 4030387200 from
          CFSG.Sporadic.He.card_He]
        decide
    have hK331 : InS3.K331 := InS3.k331_of_residue InS3.k331Residue_holds
    have hK35w : UCK.K35w := UCK.k35w_holds
    have hKZ : PartOne.Section8.StronglyEmbeddedCentralFree :=
      PartOne.Section8.stronglyEmbeddedCentralFree_holds
    have hU7T : PartTwo.Inputs1719.K_U7CentTorus := PartTwo.Inputs1719.k_U7CentTorus_holds
    have hU7S : PartTwo.Inputs1719.K_U7CartanSylowAbelian :=
      PartTwo.Inputs1719.k_U7CartanSylowAbelian_holds
    have hOut := RankThreeTheoremC.kFactOutCyclic_holds
    have hSE : StronglyEmbeddedFive := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
    have hSS : StronglyEmbeddedSolvable := PartOne.Section7.stronglyEmbeddedSolvable_holds
    have hB3 : BadNoStrongThree := PartOne.Section7.badNoStrongThree_holds
    have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    have hK3 : StronglyEmbeddedThree :=
      PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
    have hSQ : StronglyEmbeddedSolvableQ :=
      PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
        UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
    have hGy : Global22yNo := global22yNo_holds
    have hGi : Global22i :=
      { toGlobal22e := hGy.toGlobal22e
        griess := hGy.griess
        nativeGriess := hGy.nativeGriess
        exclRes := ⟨uc22pwlie_lin_holds, uc22pwliu_unitary_holds, uc22pwliu_u54_holds,
          uc22pwex_e_holds⟩
        twoRes := ⟨uc22pwlie_lin3_holds, uc22pwliu_unitary3_holds,
          uc22pwex_d4_holds hGy.nativeGriess, uc22pwex_f4_holds hGy.nativeGriess,
          uc22pwex_d4two_holds hGy.nativeGriess⟩
        diagram := uc22p20uDiagramInput_holds }
    have hGh : Global22h := hGi.toGlobal22h
    intro G _ _ hS hU S hMS hPart
    have hst := h G hS hU S hMS hPart
    have hs := Standing22.ofSetup4 hS hU S hMS hPart.1 hGy.k36
      (frob4Prime_holds frobKFacts_holds hS hU S)
    have h206 := s20_6_dataOfSetup4_of_k331 hK331 hSE hS hU S hMS hPart
    have h201 := s20_1_124 _ hs.r6_6 hGh.listB_nonabelian
    have h207 : S20_7 (UC6.dataOfSetup4 hS hU S) :=
      uc22p20q_s20_7_of (uc22p20r_global22f_of_tables hGh.griess hGh.nativeGriess hGh.excl hGh.two)
        hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 : S21_1 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      uc22p22r_s21_1_of_k108H207 _ _ F10.k108H207_holds h201
        (uc22m22_s20_4 _ hGy.toGlobal22e hs.r6_6) h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    have he : 3 < CFSG.Open.evenRank G := by
      have := hS.rank
      omega
    have hC76 := PartOne.Section7.c76Three_of_inputs hSE hK3 hB3 hS hU S
    have hUse := UC6.r77Use_dataOfSetup4_of_K36_of_C76Three hSE hGy.k36 hS hU S hMS hPart.1 hC76
    have h614 := (UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1
    have h76 : F07.R76Sig (UC6.dataOfSetup4 hS hU S) := fun p hp _ hsp => by
      by_cases h3 : 3 ∈ CFSG.Open.uniqueFourBeta G
      · exact hC76 hMS h3 p hp hsp
      · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
    have h82 := r82_dataOfSetup4 hS hU S hPart.2.2
    have h5 : S21_5 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      s21_5_setup4 hSQ hSE hK3 hB3 KBridge.kThinSimple_holds hS hU S hMS h82
        (s21_15Two_four_certificate113 _ _ h211 hs.sigmaStd he hs.dataExt.four_le hUse.1 h614
          (fun p hp hsp => h76 p hp ((UC6.dataOfSetup4 hS hU S).sig_prime p hp).2 hsp))
    have hR10 : S21_3Rest10 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      s21_3Rest10_of_rest11 hgr hS hU S hMS hPart hSE hSS hK3 hB3 hOut _
        (s21_3Rest11_of_rest12 hgr hS hU S hMS hPart hSE hSS hK3 hB3 hOut _
          (s21_3Rest12_of_rest13 hgr hS hU S hMS hPart hSE hSS hK3 hB3 hOut _
            (s21_3Rest13_of_rest14 hgr hS hU S hMS hPart hSE hOut _
              (s21_3Rest14_of_rest15 hgr hK35w hKZ hS hU S hMS hPart hSE hSS hK3 hB3 hOut _
                hst.s21_3Rest15))))
    have hR8 : S21_3Rest8 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      s21_3Rest8_of_rest9 (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
        (s21_3Rest9_of_rest10 hgr hS hU S hMS hPart hSE hSS hB3
          (UC6S846.r846_dataOfSetup4 hgr hS hU S hPart hUse.1) _ hR10)
    have hR7 : S21_3Rest7 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      s21_3Rest7_of_rest8 hS hU S hMS hPart hSE hSS hK3 hB3 hOut hgr UCK.K332Route.k33_holds
        CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple _ hR8
    have h213R3 : S21_3Rest3 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      s21_3Rest3_of_rest4 hgr
        PartTwo.Inputs1719.k_SporadicCoverCenterOdd_holds
        (s21_3Rest4_of_rest5 hS hU S hMS hSE hOut hout _
          (s21_3Rest5_of_rest6 hS hU S hMS hSE hOut hrank hout
            PartTwo.Inputs1719.k_SporadicCoverCenterOdd_holds _
            (s21_3Rest6_of_rest7 hgr hR7)))
    have h213R := s21_3Rest_of_rest2 hS hU S hMS hPart hSE hOut hrank hout hord (fun _ _ => True)
      (s21_3Rest2_of_rest3 hS hU S hMS hPart hSE hSS hK3 hB3 hOut hout hJHe (fun _ _ => True)
        h213R3)
    have hKF7 := kf7Use_dataOfSetup4 hSQ hSE hK3 hB3 hS hU S hMS
    have h213 := s21_3_setup4 hS hU S hKF7 hK3 hPart (fun _ _ => True) h213R
    have hn3 := uc22p20g_hn3_of hGy.excFacts _ (fun _ _ => True) h207
    have h86 : Steps86 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      hst.toSteps86 kFieldAutOdd_holds kFunSplit_holds kFunCount_holds hKA hU7T hU7S hgr hGy.nativeGriess hK35w hKZ hS hU S hMS hPart
        hSE hSS hK3 hB3 hOut _ hKF7 h76 hn3 h213 h5 h207 h82 h211 (fun _ _ _ => trivial)
    have h85 : Steps85 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      h86.toSteps85 hgr hS hU S hMS hPart hSE hSS hK3 hB3 hOut _ h76
    have h84 : Steps84 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      h85.toSteps84 hgr hS hU S hMS hPart hSE hSS hB3
        (UC6S846.r846_dataOfSetup4 hgr hS hU S hPart hUse.1) _
    have h83 : Steps83 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      h84.toSteps83 hgr hS hU S hPart _ h76 hn3 h213 h5 h82 h211 (fun _ _ _ => trivial)
    have h82' : Steps82 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      h83.toSteps82 hS hU S hMS hPart hSE hSS hK3 hB3 hOut hgr UCK.K332Route.k33_holds
        CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple _
    exact h82'.toSteps81 hSE hK3 hB3 hgr hS hU S hMS hPart _ h211

  have steps80 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G)
      (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G), S.InMSigma → PartIAt S.M →
        Steps80 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) := by
    have hK331 : InS3.K331 := InS3.k331_of_residue InS3.k331Residue_holds
    have hSE : StronglyEmbeddedFive := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
    have hB3 : BadNoStrongThree := PartOne.Section7.badNoStrongThree_holds
    have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    have hK3 : StronglyEmbeddedThree :=
      PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
    have hSQ : StronglyEmbeddedSolvableQ :=
      PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
        UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
    have hGy : Global22yNo := global22yNo_holds
    have hGi : Global22i :=
      { toGlobal22e := hGy.toGlobal22e
        griess := hGy.griess
        nativeGriess := hGy.nativeGriess
        exclRes := ⟨uc22pwlie_lin_holds, uc22pwliu_unitary_holds, uc22pwliu_u54_holds,
          uc22pwex_e_holds⟩
        twoRes := ⟨uc22pwlie_lin3_holds, uc22pwliu_unitary3_holds,
          uc22pwex_d4_holds hGy.nativeGriess, uc22pwex_f4_holds hGy.nativeGriess,
          uc22pwex_d4two_holds hGy.nativeGriess⟩
        diagram := uc22p20uDiagramInput_holds }
    have hGh : Global22h := hGi.toGlobal22h
    intro G _ _ hS hU S hMS hPart
    have hs := Standing22.ofSetup4 hS hU S hMS hPart.1 hGy.k36
      (frob4Prime_holds frobKFacts_holds hS hU S)
    have h206 := s20_6_dataOfSetup4_of_k331 hK331 hSE hS hU S hMS hPart
    have h201 := s20_1_124 _ hs.r6_6 hGh.listB_nonabelian
    have h207 : S20_7 (UC6.dataOfSetup4 hS hU S) :=
      uc22p20q_s20_7_of (uc22p20r_global22f_of_tables hGh.griess hGh.nativeGriess hGh.excl hGh.two)
        hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 : S21_1 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      uc22p22r_s21_1_of_k108H207 _ _ F10.k108H207_holds h201
        (uc22m22_s20_4 _ hGy.toGlobal22e hs.r6_6) h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    exact (steps81 G hS hU S hMS hPart).toSteps80 hSE hK3 hB3
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement hS hU S hMS hPart _ h211
      hs.sigmaStd (kf7Use_dataOfSetup4 hSQ hSE hK3 hB3 hS hU S hMS)

  have steps79 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G)
      (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G), S.InMSigma → PartIAt S.M →
        Steps79 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) := by
    have hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
        s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      intro X _ _ _ s hs ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor.two_le_pRank_three_sporadic_ne_J1
        hs ⟨e.trans b⟩
    have hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
        ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2 := by
      intro X _ _ hsimp hnc s ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds X hsimp hnc s
        ⟨e.trans b⟩
    have hK331 : InS3.K331 := InS3.k331_of_residue InS3.k331Residue_holds
    have hSE : StronglyEmbeddedFive := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
    have hB3 : BadNoStrongThree := PartOne.Section7.badNoStrongThree_holds
    have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    have hK3 : StronglyEmbeddedThree :=
      PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
    have hSQ : StronglyEmbeddedSolvableQ :=
      PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
        UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
    have hGy : Global22yNo := global22yNo_holds
    have hGi : Global22i :=
      { toGlobal22e := hGy.toGlobal22e
        griess := hGy.griess
        nativeGriess := hGy.nativeGriess
        exclRes := ⟨uc22pwlie_lin_holds, uc22pwliu_unitary_holds, uc22pwliu_u54_holds,
          uc22pwex_e_holds⟩
        twoRes := ⟨uc22pwlie_lin3_holds, uc22pwliu_unitary3_holds,
          uc22pwex_d4_holds hGy.nativeGriess, uc22pwex_f4_holds hGy.nativeGriess,
          uc22pwex_d4two_holds hGy.nativeGriess⟩
        diagram := uc22p20uDiagramInput_holds }
    have hGh : Global22h := hGi.toGlobal22h
    intro G _ _ hS hU S hMS hPart
    have hst := steps80 G hS hU S hMS hPart
    have hs := Standing22.ofSetup4 hS hU S hMS hPart.1 hGy.k36
      (frob4Prime_holds frobKFacts_holds hS hU S)
    have h206 := s20_6_dataOfSetup4_of_k331 hK331 hSE hS hU S hMS hPart
    have h201 := s20_1_124 _ hs.r6_6 hGh.listB_nonabelian
    have h207 : S20_7 (UC6.dataOfSetup4 hS hU S) :=
      uc22p20q_s20_7_of (uc22p20r_global22f_of_tables hGh.griess hGh.nativeGriess hGh.excl hGh.two)
        hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 : S21_1 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      uc22p22r_s21_1_of_k108H207 _ _ F10.k108H207_holds h201
        (uc22m22_s20_4 _ hGy.toGlobal22e hs.r6_6) h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    have he : 3 < CFSG.Open.evenRank G := by
      have := hS.rank
      omega
    have hC76 := PartOne.Section7.c76Three_of_inputs hSE hK3 hB3 hS hU S
    have hUse := UC6.r77Use_dataOfSetup4_of_K36_of_C76Three hSE hGy.k36 hS hU S hMS hPart.1 hC76
    have h614 := (UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1
    have h76 : F07.R76Sig (UC6.dataOfSetup4 hS hU S) := fun p hp _ hsp => by
      by_cases h3 : 3 ∈ CFSG.Open.uniqueFourBeta G
      · exact hC76 hMS h3 p hp hsp
      · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
    have h5 : S21_5 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      s21_5_setup4 hSQ hSE hK3 hB3 KBridge.kThinSimple_holds hS hU S hMS
        (r82_dataOfSetup4 hS hU S hPart.2.2)
        (s21_15Two_four_certificate113 _ _ h211 hs.sigmaStd he hs.dataExt.four_le hUse.1 h614
          (fun p hp hsp => h76 p hp ((UC6.dataOfSetup4 hS hU S).sig_prime p hp).2 hsp))
    exact hst.toSteps79 hSE RankThreeTheoremC.kFactOutCyclic_holds hrank hout
      PartTwo.Inputs1719.k_SporadicCoverCenterOdd_holds
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement hGy.excFacts hS hU S hMS _
      (fun _ _ _ => trivial) h207 h5

  have steps78 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G)
      (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G), S.InMSigma → PartIAt S.M →
        Steps78 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) := by
    have hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
        s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      intro X _ _ _ s hs ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor.two_le_pRank_three_sporadic_ne_J1
        hs ⟨e.trans b⟩
    have hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
        ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2 := by
      intro X _ _ hsimp hnc s ⟨e⟩
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
      exact CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds X hsimp hnc s
        ⟨e.trans b⟩
    have hord : ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName),
        (s = .M11 ∨ s = .M22 ∨ s = .M23 ∨ s = .HS) → IsSpor X s → ¬ 27 ∣ Nat.card X := by
      intro X _ _ s hs ⟨e⟩
      rw [Nat.card_congr e.toEquiv]
      rcases hs with rfl | rfl | rfl | rfl
      · rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) = 7920 from
          CFSG.Sporadic.Mathieu.card_M11]
        decide
      · rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 from
          CFSG.Sporadic.Mathieu.card_M22]
        decide
      · rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M23) = 10200960 from
          CFSG.Sporadic.Schreier.m23_card]
        decide
      · rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .HS) = 44352000 from
          CFSG.Sporadic.HS.card_HS]
        decide
    have hJHe : ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName),
        (s = .J2 ∨ s = .He) → IsSpor X s → 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) ∧
          ¬ 125 ∣ Nat.card X ∧ 3600 < Nat.card X := by
      intro X _ _ s hs ⟨e⟩
      have : Finite (CFSG.Blueprint.NativeSporadic.Carrier s) := Finite.of_equiv X e.toEquiv
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) e,
        Nat.card_congr e.toEquiv]
      rcases hs with rfl | rfl
      · obtain ⟨x, y, -, hx, hy, hxy, hc, -⟩ := CFSG.SectionRank.J2_sylow5_square_witness
        refine ⟨CFSG.SectionRank.QTK.two_le_pRank_of_square Nat.prime_five hx hy hxy hc, ?_⟩
        rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J2) = 604800 from
          CFSG.Sporadic.J2.card_J2]
        decide
      · obtain ⟨x, y, -, hx, hy, hxy, hc, -⟩ := CFSG.SectionRank.He_sylow5_square_witness
        refine ⟨CFSG.SectionRank.QTK.two_le_pRank_of_square Nat.prime_five hx hy hxy hc, ?_⟩
        rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) = 4030387200 from
          CFSG.Sporadic.He.card_He]
        decide
    have hK331 : InS3.K331 := InS3.k331_of_residue InS3.k331Residue_holds
    have hSE : StronglyEmbeddedFive := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
    have hSS : StronglyEmbeddedSolvable := PartOne.Section7.stronglyEmbeddedSolvable_holds
    have hB3 : BadNoStrongThree := PartOne.Section7.badNoStrongThree_holds
    have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    have hK3 : StronglyEmbeddedThree :=
      PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
    have hSQ : StronglyEmbeddedSolvableQ :=
      PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
        UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
    have hGy : Global22yNo := global22yNo_holds
    have hGi : Global22i :=
      { toGlobal22e := hGy.toGlobal22e
        griess := hGy.griess
        nativeGriess := hGy.nativeGriess
        exclRes := ⟨uc22pwlie_lin_holds, uc22pwliu_unitary_holds, uc22pwliu_u54_holds,
          uc22pwex_e_holds⟩
        twoRes := ⟨uc22pwlie_lin3_holds, uc22pwliu_unitary3_holds,
          uc22pwex_d4_holds hGy.nativeGriess, uc22pwex_f4_holds hGy.nativeGriess,
          uc22pwex_d4two_holds hGy.nativeGriess⟩
        diagram := uc22p20uDiagramInput_holds }
    have hGh : Global22h := hGi.toGlobal22h
    intro G _ _ hS hU S hMS hPart
    have hst := steps79 G hS hU S hMS hPart
    have hs := Standing22.ofSetup4 hS hU S hMS hPart.1 hGy.k36
      (frob4Prime_holds frobKFacts_holds hS hU S)
    have h206 := s20_6_dataOfSetup4_of_k331 hK331 hSE hS hU S hMS hPart
    have h201 := s20_1_124 _ hs.r6_6 hGh.listB_nonabelian
    have h207 : S20_7 (UC6.dataOfSetup4 hS hU S) :=
      uc22p20q_s20_7_of (uc22p20r_global22f_of_tables hGh.griess hGh.nativeGriess hGh.excl hGh.two)
        hGh.listB_nonabelian hGh.dichotomy _ h201 h206
    have h211 : S21_1 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      uc22p22r_s21_1_of_k108H207 _ _ F10.k108H207_holds h201
        (uc22m22_s20_4 _ hGy.toGlobal22e hs.r6_6) h207 (UC6.r6_40_2_holds hGy.u2 hGy.s25 _)
    have h213R3 : S21_3Rest3 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
      s21_3Rest3_of_rest4 CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
        PartTwo.Inputs1719.k_SporadicCoverCenterOdd_holds
        (s21_3Rest4_of_rest5 hS hU S hMS hSE RankThreeTheoremC.kFactOutCyclic_holds hout _
          hst.s21_3Rest)
    have h213R := s21_3Rest_of_rest2 hS hU S hMS hPart hSE RankThreeTheoremC.kFactOutCyclic_holds
      hrank hout hord (fun _ _ => True)
      (s21_3Rest2_of_rest3 hS hU S hMS hPart hSE hSS hK3 hB3
        RankThreeTheoremC.kFactOutCyclic_holds hout hJHe (fun _ _ => True) h213R3)
    have h213 := s21_3_setup4 hS hU S (kf7Use_dataOfSetup4 hSQ hSE hK3 hB3 hS hU S hMS) hK3 hPart
      (fun _ _ => True) h213R
    exact hst.toSteps78 hSE hK3 hB3
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
      RankThreeTheoremC.kFactOutCyclic_holds hout hGy.excFacts (uc22p20r_u38_of_griess hGy.griess)
      hGh.listB_nonabelian CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
      PartTwo.thinList13_holds PartTwo.Inputs1719.k_LieModelNotL2_holds hS hU S hMS hPart _
      (fun _ _ _ => trivial) h211 h207 h213

  exact theorem2219Four_of_steps78_holds
    (UCK.K332Route.k332Cyc_of_rows UCK.K332Route.k33_holds
      (UCK.K332Route.k332Rows_of_rest UCK.K332Route.k332RowsRest_holds))
    (F10.k105Spor_of_rest
      (F10.k105SporRest_of_restB (F10.k105SporRestB_of_restE F10.k105SporRestE_holds))) steps78


theorem theorem2219Four_setup_frontier
    : Theorem2219Four :=
  theorem2219Four_of_setup_frontier kLieBorelAutPrime_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22
