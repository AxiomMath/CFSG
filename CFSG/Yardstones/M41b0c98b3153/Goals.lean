module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7Q
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6Main
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductHolds
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LargeMain
public import CFSG.LocalAnalysis.EvenBN.G2.LargeMain
public import CFSG.LocalAnalysis.EvenBN.G2.FourMain
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.QTwoLayer
public import CFSG.LocalAnalysis.SteinbergSFSingleCommExclusion
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHDstarB
public import CFSG.LocalAnalysis.SteinbergSFSingleCommEmbedded
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixK
public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusion
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBPComm
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBPFactors
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBPGen
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBPHGen
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBPModelN3
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBPNonSwap
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBPNormTP
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBPPerfect
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBPQuasi
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBPSInv
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofElevenNotTrans
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofModelTI
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSwap
public import CFSG.LocalAnalysis.EvenBN.U5.LinMain
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PSlot
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Holds
public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49EHolds
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Closed

public section

namespace CFSG.Yardstones.M41b0c98b3153

theorem u5LinearCaseExclusion :
    U5LinearCaseExclusion :=
  CFSG.LocalAnalysis.EvenBN.U5.u5LinearCaseExclusion_holds

open CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.EvenBN.U5.CaseBParts in
theorem u5ProductCaseExclusion :
    U5ProductCaseExclusion :=
  u5ProductCaseExclusion_of_parts
    { s8 := su3SylowTI, s8l3 := l3AutOdd, s8l3d := l3Dihedral, s38a1 := sec38a1, s38a2 := sec38a2, s38b := sec38Input,
      s38c := sec38NotNormal, s38o := sec38Odd, s38d := sec38Layer,
      s39a1 := sec39a1, s39a := sec39a, s39b := sec39b, s39c := sec39c, s39d := sec39d,
      s39e := sec39e, s39i := sec39Input, s39n := sec39NotNormal, s39r := sec39Reduced,
      s39l := sec39Layer, s39o := sec39LOne, s39dd := sec39Odd,
      s310o := sec3101Orders, s310a1 := sec3101A1, s310a2 := sec3101A2, s310e := sec3101E,
      s310b := sec3101B, s310c := sec3102, s310d := sec310Three,
      s311a := sec311Trans, s311b := sec311NotTrans,
      s312a := sec312A, s312b := sec312B, s313a := sec313Trans, s313b := sec313NotTrans }
    { p11 := sec52Sylow, p12 := sec52Factors, p13 := sec52SInv, p14 := sec52Gen, p15 := sec52Comm,
      p16 := sec52, p21 := hGen, p22 := normalizerTP, p3 := perfectNormalizer,
      p41 := involutoryFixedElemAb, p42 := nonSwap }

theorem gomiU42Input :
    CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Input :=
  CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.gomiU42Input_holds

theorem gomiLemma1PInput :
    CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiLemma1PInput :=
  CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.gomiLemma1PInput_holds

theorem u52UnitaryCaseExclusion :
    U52UnitaryCaseExclusion :=
  CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.u52UnitaryCaseExclusion_holds

theorem u52LinearSmallCentralizerExclusion :
    U52LinearSmallCentralizerExclusion :=
  CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.u52LinearSmallCentralizerExclusion_holds

open CFSG.LocalAnalysis.EvenBN.GMSK CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts in
theorem sp4SingleCommutatorExclusion :
    CFSG.LocalAnalysis.EvenBN.Sp4.SingleCommutatorExclusion :=
  have hSel : FixedRootSelector fun D _ => CFSG.Blueprint.Catalog D :=
    catalog_selector fixedRootSelector_alternating fixedRootSelector_oddLieType
      fixedRootSelector_evenLieType Sporadic.fixedRootSelector_sporadicRep
  CFSG.LocalAnalysis.EvenBN.Sp4.singleCommutatorExclusion_of_parts (sixH hSel) (six_Emb hSel)
    (six_K hSel) (field_fusion hSel) canonicity

theorem sp4BothTrivialProductExclusion :
    CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases.BothTrivialProductExclusion :=
  CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProduct.bothTrivialProductExclusion_holds

theorem sp4BothTrivialOddFieldNoSwap :
    CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases.BothTrivialOddFieldNoSwap :=
  CFSG.LocalAnalysis.EvenBN.Sp4.bothTrivialOddFieldNoSwap_holds

theorem g2FourCenterlessExclusion :
    G2FourCenterlessExclusion :=
  LocalAnalysis.EvenBN.G2.g2FourCenterlessExclusion_holds

theorem g2LargeCenterlessExclusion :
    G2LargeCenterlessExclusion :=
  LocalAnalysis.EvenBN.G2.g2LargeCenterlessExclusion_holds

theorem trialityD4TwoCenterlessExclusion :
    TrialityD4TwoCenterlessExclusion := by
  intro G _ _ _ hnonab hK L hL hZ hcore hcyc hm
  obtain ⟨t, h⟩ := LocalAnalysis.EvenBN.TrialityD4.exists_setup hnonab hK hL hZ hcore hcyc le_rfl hm
  obtain ⟨d⟩ := LocalAnalysis.EvenBN.TrialityD4.nonempty_trialityD4Data_of_lieModel le_rfl hm
  exact h.false_of_odd_of_layerHyp d (h.layerHyp_two d rfl) odd_one

theorem trialityD4LargeCenterlessExclusion :
    TrialityD4LargeCenterlessExclusion :=
  LocalAnalysis.EvenBN.TrialityD4.trialityD4LargeCenterlessExclusion_holds

theorem titsThm49FailureExclusion :
    CFSG.LocalAnalysis.EvenBN.Tits.Thm49FailureExclusion :=
  CFSG.LocalAnalysis.EvenBN.Tits.Thm49E.thm49FailureExclusion_holds

theorem titsThm49StatementExclusion :
    TitsThm49StatementExclusion :=
  CFSG.LocalAnalysis.EvenBN.Tits.N.titsThm49StatementExclusion_holds

end CFSG.Yardstones.M41b0c98b3153
