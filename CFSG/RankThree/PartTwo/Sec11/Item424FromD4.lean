module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairingHolds
public import CFSG.RankThree.PartTwo.Sec4.Item424Res7ProofG2
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowCensus
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowLargePrime
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowMcLON
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof424Use
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed
import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofLinear
import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofUnitary
public import CFSG.RankThree.PartTwo.Sec4.Item424Res4ProofSp
public import CFSG.RankThree.PartTwo.Sec4.Item424Res4ProofRee
public import CFSG.RankThree.PartTwo.Sec4.Item417Res8ProofTriality
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent.Holds
public import CFSG.RankThree.PartTwo.Sec4.Item424Res6Proof
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.Main
public import CFSG.RankThree.PartTwo.Sec4.Item424Res5Proof
public import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2Proof
public import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofEight
public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofSp62Wire
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.PairingSpor

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Bridge


theorem item4_24Used_of_item4_24M' (h : Sec4.Item4_24M) : Sec4.Item4_24Used := by
  intro G _ _ hG A hAmax hA27 hEF L hL a ha3 haZ hCA c hcA hca K hK hKT hN
  rcases h G hG A hAmax hA27 hEF L hL a ha3 haZ hCA c hcA hca K hK hKT hN with
    ⟨hf, hS⟩ | ⟨hG2, hD⟩ | ⟨hL3, hS⟩ | ⟨hMH, -, hD⟩
  · exact ⟨Or.inl hS, Or.inl hf⟩
  · refine ⟨Or.inr hD, Or.inr ?_⟩
    rcases hG2 with ⟨q, hq, ⟨e⟩⟩ | ⟨q, hq, ⟨e⟩⟩
    · exact ⟨_, inferInstance, Or.inl ⟨q, hq, ⟨MulEquiv.refl _⟩⟩, ⟨e⟩⟩
    · exact ⟨_, inferInstance, Or.inr (Or.inl ⟨q, hq, ⟨MulEquiv.refl _⟩⟩), ⟨e⟩⟩
  · refine ⟨Or.inl hS, Or.inr ?_⟩
    rcases hL3 with ⟨p, e', hp, he, ⟨hpe, ⟨e⟩⟩ | ⟨hpe, ⟨e⟩⟩⟩ |
      ⟨π, p, f, K', hK', hPF, hmod, ⟨e⟩⟩
    · exact ⟨_, inferInstance,
        Or.inr (Or.inr (Or.inl ⟨p, e', hp, he, Or.inl ⟨hpe, ⟨MulEquiv.refl _⟩⟩⟩)), ⟨e⟩⟩
    · exact ⟨_, inferInstance,
        Or.inr (Or.inr (Or.inl ⟨p, e', hp, he, Or.inr ⟨hpe, ⟨MulEquiv.refl _⟩⟩⟩)), ⟨e⟩⟩
    · exact ⟨_, inferInstance,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨π, p, f, K', hK', hPF, hmod, ⟨MulEquiv.refl _⟩⟩))), ⟨e⟩⟩
  · refine ⟨Or.inr hD, Or.inr ?_⟩
    rcases hMH with hM | hH
    · exact ⟨CFSG.Blueprint.NativeSporadic.M24, inferInstance,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨MulEquiv.refl _⟩)))), hM⟩
    · exact ⟨CFSG.Blueprint.NativeSporadic.He, inferInstance,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨MulEquiv.refl _⟩)))), hH⟩

end Bridge

section Main


theorem item4_24M_holds
    : Sec4.Item4_24M :=
  let hT : D4PairingTransTwo := d4PairingTransTwo_holds
  let hD4 : Sec4.K424PairingD4 := k424PairingD4_of (d4PairingE9_of hT)
  let hL : Sec4.K424PairingLie := Sec4.Res424Seven.k424PairingLie_of_d4 hD4
  let hGA := CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  let h46 : Sec4.Item4_6 := Sec4.Census.rank3II_4_6_of_griess_narrow41
    (Sec4.Item41Narrow.item4_1LargePrime_of_griess hGA)
    (Sec4.Item41Narrow.item4_1ThreeCover_of_griess hGA) hGA
    (Sec4.Census.coverCenterThreeRest_of hGA)
  Sec4.item4_24M_of Sec4.rank3II_4_5 h46 (Sec4.rank3II_4_7W_of h46)
    (Sec4.k424FieldCent_of (Sec4.k424FieldCentNotL2_of Sec4.k424FieldCentLinear
        Sec4.k424FieldCentUnitary Sec4.k424FieldCentSymplectic_holds
        Sec4.k424FieldCentLargeRee_holds))
    Sec4.k424TrialityOuter_holds
    Sec4.Census.Karpilovsky.Coordinator.CoverCent.k424CoverCent_holds
    (Sec4.k424SLThree_of Sec4.rank3II_4_5)
    (Sec4.k424InnerFull_of_census
      (Sec4.k424InnerCensus_of Sec4.k424Inner46One Sec4.k424Inner46Two
        (Sec4.k424Inner46Three_of hL Sec4.k424ThreeSp4_holds Sec4.k424ThreeL4_holds)
        Sec4.k424Inner46Four
        (Sec4.k424Inner46Five_of
          CFSG.AGLEmbeddingD2.Wilson.Census424Rest.k424Inner46FiveRest_holds)
        (Sec4.k424Inner46Six_of (Sec4.k424Inner46SixRest_of Sec4.k424SixSp4Odd_holds hL
          Sec8.reeF4OrderThreeConj_holds Sec4.Res417Seven.k417TitsCentThree_holds))
        Sec4.k424Inner46Seven Sec4.k424Inner46Eight_holds)
      (Sec4.k424Pairing_of hL
        CFSG.AGLEmbeddingD2.Wilson.Census424Rest.k424PairingSpor_holds))

theorem item4_24Used_holds
    : Sec4.Item4_24Used :=
  item4_24Used_of_item4_24M' item4_24M_holds

theorem item116P2bCore_holds
    : Item116P2bCore :=
  item116P2bCore_of_used item4_24Used_holds Sec4.rank3II_4_5

theorem item119_of_items
    (h112 : Item112) (h114 : Item114) (h117 : Item117) (h118 : Item118) :
    Item119 :=
  item119_of_item118_M item4_24M_holds Sec4.rank3II_4_5 h112 h114 h117 h118

end Main

end CFSG.RankThree.PartTwo.Sec11
