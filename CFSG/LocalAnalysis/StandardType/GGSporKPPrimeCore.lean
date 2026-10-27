module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA
public import CFSG.Sporadic.Bridge.BBound
public import CFSG.Sporadic.Bridge.MonsterModels
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAClose
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMPairs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSeven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Five
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenEbarData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenEbarData
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Perm.ChainByOrder
public import CFSG.RankThree.CentralExtension.PrimeToPKernel
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.Native.FiveLocalAction
public import CFSG.RankThree.Native.FiveLocalForms
public import CFSG.RankThree.Native.FiveLocalInterface
public import CFSG.RankThree.PartOne.K1214.OmegaAlg
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Fi23.StarKernel
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate13622Base
public import Certificates.Certificate16005
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem bmPPrimeCore_of_oPrimeCoreTrivialAt {p : ℕ} {K : Type} [Group K] [Finite K]
    (h : OPrimeCoreTrivialAt p K) : BMPPrimeCore p K := by
  intro x hx _
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp (h x hx)

theorem ggSporK_bmPPrimeCore_B_three [Finite (TauCeti.CFSGIndex.sporadic .B).Group] :
    BMPPrimeCore 3 (TauCeti.CFSGIndex.sporadic .B).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  let e' : CFSG.Blueprint.NativeSporadic.B ≃* (TauCeti.CFSGIndex.sporadic .B).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite CFSG.Blueprint.NativeSporadic.B := Finite.of_equiv _ e'.symm.toEquiv
  have h : OPrimeCoreTrivialAt 3 CFSG.Blueprint.NativeSporadic.B :=
    BThreeFi23.oPrimeCoreTrivialAt_B_three
  have h' : BMPPrimeCore 3 CFSG.Blueprint.NativeSporadic.B :=
    bmPPrimeCore_of_oPrimeCoreTrivialAt h
  exact @bmPPrimeCore_of_mulEquiv CFSG.Blueprint.NativeSporadic.B
    (TauCeti.CFSGIndex.sporadic .B).Group _ _ _ _ 3 e' h'

theorem ggSporK_bmPPrimeCore_B_five [Finite (TauCeti.CFSGIndex.sporadic .B).Group] :
    BMPPrimeCore 5 (TauCeti.CFSGIndex.sporadic .B).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  let e' : CFSG.Blueprint.NativeSporadic.B ≃* (TauCeti.CFSGIndex.sporadic .B).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite CFSG.Blueprint.NativeSporadic.B := Finite.of_equiv _ e'.symm.toEquiv
  have h : OPrimeCoreTrivialAt 5 CFSG.Blueprint.NativeSporadic.B := oPrimeCoreTrivialAt_B_five
  have h' : BMPPrimeCore 5 CFSG.Blueprint.NativeSporadic.B :=
    bmPPrimeCore_of_oPrimeCoreTrivialAt h
  exact @bmPPrimeCore_of_mulEquiv CFSG.Blueprint.NativeSporadic.B
    (TauCeti.CFSGIndex.sporadic .B).Group _ _ _ _ 5 e' h'

private theorem gkG_bmPPrimeCore_M_of_holds {p : ℕ} (h : SporadicOPrimeHolds .M p)
    [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    (hS : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group)
    (e : CFSG.Blueprint.NativeSporadic.MonsterModel.y443Derived.Carrier ≃*
      (TauCeti.CFSGIndex.sporadic .M).Group) :
    BMPPrimeCore p (TauCeti.CFSGIndex.sporadic .M).Group :=
  bmPPrimeCore_of_oPrimeCoreTrivialAt (h _ ⟨e.symm⟩)

theorem ggSporK_bmPPrimeCore_M_three_of_simple [Finite (TauCeti.CFSGIndex.sporadic .M).Group] :
    IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group →
      BMPPrimeCore 3 (TauCeti.CFSGIndex.sporadic .M).Group := by
  intro hS
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  exact gkG_bmPPrimeCore_M_of_holds (sporadicOPrimeHolds_M_of_gmat
    (oPrimeCoreTrivialAt_gmat_of_uninverted Nat.prime_three (by norm_num)
      (uninvertedOPrimeTrivial_gmat_of_twoAPureKlein Nat.prime_three (by norm_num)
        BThreeFi23.oPrimeCoreTrivialAt_B_three ThreeBNF.twoAPureKlein_three_Gmat))) hS e

theorem ggSporK_bmPPrimeCore_M_five_of_simple [Finite (TauCeti.CFSGIndex.sporadic .M).Group] :
    IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group →
      BMPPrimeCore 5 (TauCeti.CFSGIndex.sporadic .M).Group := by
  intro hS
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  exact gkG_bmPPrimeCore_M_of_holds (sporadicOPrimeHolds_M_of_gmat
    (oPrimeCoreTrivialAt_gmat_of_uninverted Nat.prime_five (by norm_num)
      (uninvertedOPrimeTrivial_gmat_of_twoATwoCommuting Nat.prime_five (by norm_num)
        oPrimeCoreTrivialAt_B_five sporadicOPrimeHolds_Co1_five
        MonsterFiveGmat.twoATwoCommuting_five_Gmat))) hS e

theorem ggSporK_bmPPrimeCore_M_seven_of_simple [Finite (TauCeti.CFSGIndex.sporadic .M).Group] :
    IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group →
      BMPPrimeCore 7 (TauCeti.CFSGIndex.sporadic .M).Group := by
  intro hS
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  exact gkG_bmPPrimeCore_M_of_holds (sporadicOPrimeHolds_M_of_gmat
    (oPrimeCoreTrivialAt_seven_Gmat_of_classes MonsterSevenCensus.monsterSevenClasses)) hS e

theorem ggSporK_bmPPrimeCore_M_thirteen_of_simple [Finite (TauCeti.CFSGIndex.sporadic .M).Group] :
    IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group →
      BMPPrimeCore 13 (TauCeti.CFSGIndex.sporadic .M).Group := by
  intro hS
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  exact gkG_bmPPrimeCore_M_of_holds (sporadicOPrimeHolds_M_thirteen_of bThirteenOddCore_holds) hS e

end CFSG.StandardType.SporadicShape
