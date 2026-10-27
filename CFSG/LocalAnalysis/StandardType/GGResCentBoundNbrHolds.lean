module

public import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrConj
public import CFSG.LocalAnalysis.StandardType.GGResCentBound
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc11R
public import CFSG.LocalAnalysis.StandardType.GGRemStdSubTableBHolds
public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGRound12
public import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrCaseIISplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6A5KLine
public import CFSG.LocalAnalysis.StandardType.GGTwE6A5LKnownHolds
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourOutLine
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1Holds
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLSplitDispatch
public import CFSG.LocalAnalysis.StandardType.GGTwE6LocalRankHolds
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrCaseII
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
public import CFSG.LocalAnalysis.StandardType.GGResRowAssembly
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeNarrow
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I61
import CFSG.RankThree.PartOne.K1214.Omega
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1ThreeA2Two

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTwE6ThreeNbrRankInput_holds : GGTwE6ThreeNbrRankInput := by
  have h01 : CFSG.Yardstones.M3f9567aba59d.GGRemainderStdSubTableB :=
    ggRemainderStdSubTableB_proved
  obtain ⟨hTE6L, -, hsR, -⟩ := h01
  have hTE6 := ggTableBTwE6Round12_of_lang hTE6L
  have hP := ggStdSubPrimeInput_of_round12 hTE6 TwF4SUThree.ggTwF4ThreeRankInput_holds hsR
  have hLB := ggLBalanceInput_of_catalogueSchreier
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hR4 : GGTwE6ThreeSCFourNotTwoLocalOddInput :=
    ggTwE6ThreeSCFourNotTwoLocalOddInput_of_kga1
      NoOffTwE6Three.ggTwE6ThreeTwoLocalInnToralInput_holds
      TwE6LemmaK.ggTwE6ThreeToralTypeMinusOneInput
      ggTwE6ThreeNoRankSixInput_holds
  have hII : GGTwE6ThreeNbrCaseII := ggTwE6ThreeNbrCaseII_of_knownSplit hLB hP
    SCFourCover.ggTwE6SCFourLabelsKnown_holds SCFourCover.ggTwE6SCFourOutKnown_holds
    SCFourCover.ggTwE6A5KKnown_holds SCFourCover.ggTwE6OfOutsideSplitKnown_holds
    SCFourCover.ggTwE6A5LKnown_holds
    (ggTwE6ThreeBstarRankInput_of_known (ggTwE6ThreeSCFourNotTwoLocalInput_of_odd hR4))
  exact ggTwE6ThreeNbrRankInput_of_caseII hII
    ggTwE6LocalRankInput_holds ggLabelCenterPCyclicInput_holds

theorem ggResXDichotomyInput_holds : GGResXDichotomyInput := by
  have h01 : CFSG.Yardstones.M3f9567aba59d.GGRemainderStdSubTableB :=
    ggRemainderStdSubTableB_proved
  obtain ⟨hTE6L, -, hsR, -⟩ := h01
  have hTE6 := ggTableBTwE6Round12_of_lang hTE6L
  have hP := ggStdSubPrimeInput_of_round12 hTE6 TwF4SUThree.ggTwF4ThreeRankInput_holds hsR
  have hLB := ggLBalanceInput_of_catalogueSchreier
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hRig := ggLabelRigidInput_holds
  have hTCJ : GGTCJKnown := TCJ.ggTCJKnown_holds
  have hRk : GGTwE6ThreeNbrRankInput := ggTwE6ThreeNbrRankInput_holds
  have hT : GGTBTorAll := ggTBTorAll_of_remaining trivial
  have hLift : GGTBTorLiftRows := ggTBTorLiftRows_holds
  have hRR : GGTBXDatumResInputRest :=
    ggTBXDatumResInputRest_of_rows hRig ggLabelCenterPCyclicInput_holds hRk
  have hR : GGTBXDatumResInput := ggTBXDatumResInput_of_rest hRig hLB hP hRR
  have hraw : GGRawInnFieldInput := ggRawInnFieldInput_of_rest_omega ggRawInnFieldOn_rest5
  have hiso : GGRawInndiagIsoInput :=
    ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)
  have hSub : GGNbrSubcomponentInput := ggNbrSubcomponentInput_of_lBalance hLB hP
  have hX : GGResXDichotomyInput :=
    ggResXDichotomy_of_res hRig hraw hiso hTCJ hSub hT hLift hR
  exact hX

theorem ggResCentBoundInput_holds : GGResCentBoundInput :=
  ggResCentBoundInput_of_xDichotomy ggLNoncyclicInput_holds
    ggResXDichotomyInput_holds TCJ.ggTCJKnown_holds ggLabelRigidInput_holds
    ggTBFixInput_holds

theorem ggResCentBoundNbrInput_holds : GGResCentBoundNbrInput := by
  have h01 : CFSG.Yardstones.M3f9567aba59d.GGRemainderStdSubTableB :=
    ggRemainderStdSubTableB_proved
  obtain ⟨hTE6L, -, hsR, -⟩ := h01
  have hTE6 := ggTableBTwE6Round12_of_lang hTE6L
  have hP := ggStdSubPrimeInput_of_round12 hTE6 TwF4SUThree.ggTwF4ThreeRankInput_holds hsR
  have hLB := ggLBalanceInput_of_catalogueSchreier
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hRig := ggLabelRigidInput_holds
  have hTCJ : GGTCJKnown := TCJ.ggTCJKnown_holds
  have hRk : GGTwE6ThreeNbrRankInput := ggTwE6ThreeNbrRankInput_holds
  have hT : GGTBTorAll := ggTBTorAll_of_remaining trivial
  have hLift : GGTBTorLiftRows := ggTBTorLiftRows_holds
  have hRR : GGTBXDatumResInputRest :=
    ggTBXDatumResInputRest_of_rows hRig ggLabelCenterPCyclicInput_holds hRk
  have hR : GGTBXDatumResInput := ggTBXDatumResInput_of_rest hRig hLB hP hRR
  have hraw : GGRawInnFieldInput := ggRawInnFieldInput_of_rest_omega ggRawInnFieldOn_rest5
  have hiso : GGRawInndiagIsoInput :=
    ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)
  have hX : GGResXDichotomyInput := ggResXDichotomyInput_holds
  have hA8 : GGForkA8NotReflInput := ggForkA8NotReflInput_of_mp ggInnerDiagMpInput_holds
  exact ggResCentBoundNbrInput_of_known hT hLift hX hTCJ hRig hLB hP hRk hA8 hraw hiso

theorem ggNbrSubcomponentInput_proved : GGNbrSubcomponentInput := by
  have h01 : CFSG.Yardstones.M3f9567aba59d.GGRemainderStdSubTableB :=
    ggRemainderStdSubTableB_proved
  obtain ⟨hTE6L, -, hsR, -⟩ := h01
  have hTE6 := ggTableBTwE6Round12_of_lang hTE6L
  have hP : GGStdSubPrimeInput :=
    ggStdSubPrimeInput_of_round12 hTE6 TwF4SUThree.ggTwF4ThreeRankInput_holds hsR
  have hLB : GGLBalanceInput :=
    ggLBalanceInput_of_catalogueSchreier
      CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  exact ggNbrSubcomponentInput_of_lBalance hLB hP

theorem GGResHyp.J_le_K_of_original {p : ℕ} [Fact p.Prime]
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : J ≤ K :=
  ggNbrSubcomponentInput_proved G p B x L D J hH.1.1 hH.1.2.2 y K hH.2.2.2.2.1

theorem GGResHyp.J_le_K_of_subcomponent {p : ℕ} [Fact p.Prime]
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hsub : GGNbrSubcomponentInput) : J ≤ K :=
  hsub G p B x L D J hH.1.1 hH.1.2.2 y K hH.2.2.2.2.1

theorem GGResHyp.J_component_CK_of_subcomponent {p : ℕ} [Fact p.Prime]
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hsub : GGNbrSubcomponentInput) :
    IsComponentOf (J.subgroupOf K)
      (ggAutFixedSubgroup (K.normalizerMonoidHom
        ⟨x⁻¹, inv_mem (by
          exact (GGInnerDiagOn.le_normalizer
            (hH.2.2.1.2 y K hH.2.2.2.2.1)) hH.1.tableB_facts.2.2.1)⟩)) := by
  classical
  have hJK : J ≤ K := GGResHyp.J_le_K_of_subcomponent hH hsub
  have hKmark : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hxN : x ∈ Subgroup.normalizer (K : Set G) :=
    GGInnerDiagOn.le_normalizer hKmark hxBs
  have hJc : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr (hS := hH.1.1.2.2.2.2.2.2.1)
      (hDJ := hH.1.2.2) (hnbr := hH.2.2.2.2.1) hJK
  have hcomp := isComponentOf_subgroupOf_ggAutFixed hxN hJK hJc
  have hfix : ggAutFixedSubgroup (K.normalizerMonoidHom ⟨x⁻¹, inv_mem hxN⟩) =
      ggAutFixedSubgroup (K.normalizerMonoidHom ⟨x, hxN⟩) := by
    ext k
    constructor
    · intro hk
      have hk' : ((K.normalizerMonoidHom ⟨x⁻¹, inv_mem hxN⟩ k : ↥K) : G) = (k : G) :=
        congrArg Subtype.val hk
      rw [normalizerMonoidHom_apply_coe] at hk'
      have hk'' : x⁻¹ * (k : G) * x = (k : G) := by
        simpa only [inv_inv] using hk'
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_coe]
      have hconj := congrArg (fun z : G => x * z * x⁻¹) hk''
      have hleft : x * (x⁻¹ * (k : G) * x) * x⁻¹ = (k : G) := by group
      exact hconj.symm.trans hleft
    · intro hk
      have hk' : ((K.normalizerMonoidHom ⟨x, hxN⟩ k : ↥K) : G) = (k : G) :=
        congrArg Subtype.val hk
      rw [normalizerMonoidHom_apply_coe] at hk'
      have hk'' : x * (k : G) * x⁻¹ = (k : G) := by
        simpa only [inv_inv] using hk'
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_coe]
      have hconj := congrArg (fun z : G => x⁻¹ * z * x) hk''
      have hleft : x⁻¹ * (x * (k : G) * x⁻¹) * x = (k : G) := by group
      simpa only [inv_inv] using hconj.symm.trans hleft
  simpa [hfix] using hcomp

theorem GGResHyp.J_component_CK_of_original {p : ℕ} [Fact p.Prime]
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    IsComponentOf (J.subgroupOf K)
      (ggAutFixedSubgroup (K.normalizerMonoidHom
        ⟨x⁻¹, inv_mem (by
          exact (GGInnerDiagOn.le_normalizer
            (hH.2.2.1.2 y K hH.2.2.2.2.1)) hH.1.tableB_facts.2.2.1)⟩)) :=
  GGResHyp.J_component_CK_of_subcomponent hH ggNbrSubcomponentInput_proved

end CFSG.StandardType
