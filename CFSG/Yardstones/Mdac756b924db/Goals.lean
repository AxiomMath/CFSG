module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.AvoidAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.SlotsFrontierE3Rows6
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.GenerationPushingUpAssembly
public import CFSG.Yardstones.M9cbf837c48cf.SlotInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.RankOneOut.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.OuterThree.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.E9Transitive.Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.SylowThreeAbelian.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.OneImageIrr.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.ElemLe8
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.TwoSubgroups
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.TwoNormalized.Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Assembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.ThreeQuotient.Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.SylowM27.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.FieldGeneration.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkClosed
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L34Proof
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.AGL81AKFactsAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockPerfectCoreThreeHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockSylowThreeAutHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.GenericKFactsIso
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.GenericKFactsBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.OpenKFactsNoSeitz
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Main
public import CFSG.Yardstones.Mdac756b924db.FrontierRootsGF2n
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisHolds

public section

namespace CFSG.Yardstones.Mdac756b924db

theorem agl81TheoremAResiduesE3_holds
    : AGL81TheoremAResiduesE3 :=
  agl81TheoremAResiduesE3_of_gf2nType CFSG.Yardstones.Mf4cdcdf2e013.gf2n_type_statement

theorem gl83GenericL28ResiduesE3_holds :
    GL83GenericL28ResiduesE3 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.gl83GenericL28ResiduesE3_holds_of_kfacts
    CFSG.LocalAnalysis.RankThreeTheoremC.L28.kFactL28ThreeQuotient_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.L28.kFactOutThreeNilpotent_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.L28.kFactOutThreeCoprime_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.kFactCentralOmega_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.L28.kFactSylowM27_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.L28.kFactFieldGeneration_holds

theorem gl83GenericU3Lemma43E3_holds :
    GL83GenericU3Lemma43E3 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.gl83GenericU3Lemma43E3_holds_of_heis3
    CFSG.LocalAnalysis.RankThreeTheoremC.kFactWeakClosureHeisThree_holds

theorem gl83GenericA6Lemma43E3_holds :
    GL83GenericA6Lemma43E3 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.gl83P3A6_holds_of_kfacts
    CFSG.LocalAnalysis.RankThreeTheoremC.A6.kFact1435_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.kFactZJFactorizationAny_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.A6.kFact2811_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.A6.kFactPSp43ElemLe8_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.A6.kFactPSp43TwoSubgroups_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.A6.kFactA6TwoNormalized_holds

theorem gl83GenericL34RemarkE3_holds :
    GL83GenericL34RemarkE3 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.gl83P3L34_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.kFactWeakClosureOmega3_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.kFactCentralOmega_holds

theorem gl83GenericListSporE3_holds :
    GL83GenericListSporE3 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.gl83GenericListSporE3_of_i1434
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.kFactI1434_holds

theorem gl83GenericU3PlaneE3_holds :
    GL83GenericU3PlaneE3 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.gl83GenericU3PlaneE3_of_i1434
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.kFactI1434_holds

theorem gl83SmallRankProp622E3_holds
    : GL83SmallRankProp622E3 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.gl83SmallRankProp622E3_of_rows6
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal.openRows6_holds

theorem gl83SmallRankInterfaceE3_holds
    : GL83SmallRankInterfaceE3 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.gl83SmallRankInterfaceE3_of_leaves
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.outerFixedRankCross_holds _)
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.outerFixedRankCross_holds _)
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.outerFixedRankCross_holds _)
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.outerFixedRankCross_holds _)

theorem gl83SmallRankLemma630E3_holds
    : GL83SmallRankLemma630E3 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.gl83SmallRankLemma630E3_of_leaves
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.outerFixedRankCross_holds _)
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.outerFixedRankCross_holds _)
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.outerFixedRankCross_holds _)
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.outerFixedRankCross_holds _)

theorem agl81TheoremAKFacts_holds :
    AGL81TheoremAKFacts :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.agl81TheoremAKFacts_of_blocks
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.kFactBlockL28Rank_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.kFactBlockL28TwoRank_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.kFactBlockPerfectCoreThree_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.kFactBlockSylowThreeAut_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.kFactBlockHeisenbergAut_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.kFactBlockHeisenbergInner_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.kFactBlockFieldIndex_holds

theorem agl81TheoremBKFacts_holds :
    AGL81TheoremBKFacts :=
  { d2 :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.d2KFactLeavesCoreF_of_seitz_solomonTimmesfeld
        CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
        CFSG.Yardstones.M9cbf837c48cf.solomonTimmesfeldMainNonAbelian_of_slots
    blockRankOneOut :=
      CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.kFactBlockRankOneOut_holds
    blockOuterThree :=
      CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.kFactBlockOuterThree_holds
    blockE9Transitive :=
      CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.kFactBlockE9Transitive_holds
    blockPLElem :=
      CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.kFactBlockPLElem_holds
    sylowThreeAbelian :=
      CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.kFactSylowThreeAbelian_holds
    glaubermanNiles :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.glaubermanNilesInput_holds
    strongThreeAutomizer :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.kFactStrongThreeAutomizer_holds
    blockOneImageIrr :=
      CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.kFactBlockOneImageIrr3_holds
    ffModule :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.ffModuleTheorem_holds }

theorem gl83GenericKFacts_holds :
    GL83GenericKFacts :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.gl83GenericKFacts_of_statement
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.gl83GenericKFacts_unconditional

theorem gl83SmallRankKFacts_holds
    : GL83SmallRankKFacts :=
  have h := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gl83SmallRankKFacts_holds
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1⟩

end CFSG.Yardstones.Mdac756b924db
