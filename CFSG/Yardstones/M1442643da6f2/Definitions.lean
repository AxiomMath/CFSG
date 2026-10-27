module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Loc
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Rest4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HResidual
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerE1Weak
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S14Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.XFiveLemma
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsAtlas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitCompBInner
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Hyp12LieRec
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuThm54ReachHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm24OneCIT
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenSmallLie
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.StatementHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonCatM10
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonCatZ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SL7Reduce2
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lemma210Two
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.LocalStatement
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Defs
public import CFSG.LocalAnalysis.OddStandard.AltStdFormBigStdDefs
import CFSG.LocalAnalysis.ComponentClassification.HallQ8Main

public section

namespace CFSG.Yardstones.M1442643da6f2

open CFSG.EvenSporadicStandard CFSG.Blueprint.NativeSporadic

structure ConwayStandardInputs : Prop where
  fs79 : M12Std.Rbc.FS79RbcHered
  kdnp : M12Std.Rbc.KDNP
  co2 : Co2Exclusion

structure EgawaHarrisSolomonInputs : Prop where
  egawaHypA : M24Std.Ega81HypAZ2A8K
  harrisSolomon : M24Std.HarrisSolomonZ2S6IsoK

structure CatalogueFixedComponentFacts : Prop where
  kgPumpTableT : HSStd.Zassenhaus.Outer.KGPumpTableT
  noFixedDoubleCover : Induction.Balance.CatalogNoFixedDoubleCover

structure Finkelstein76bOuterCase : Prop where
  outerS16Loc : Fin76b.Fin76bOuterS16Loc
  outerS84 : Fin76b.Fin76bOuterS8₄

structure InvolutionCentralizerTheorems : Prop where
  harada39One : HSStd.Harada39One
  harada39Two : HSStd.Harada39Two
  harris311 : HSStd.Harris311
  harris311HiS : HSStd.Harris311HiS
  ghLemma53_1 : RuStd.S2.GHLemma53_1

structure ONanInputs : Prop where
  onan77S5 : HSStd.Zassenhaus.ONan77S5
  onanInspection : HSStd.Zassenhaus.ONanInspection
  onanNoSL29Y : HSStd.Zassenhaus.PartA.ONanNoSL29Y

structure CatalogueCentralizerFacts : Prop where
  catZ2A6 : CatNoAlmostSimpleZ2 (alternatingGroup (Fin 6))
  catZ2A7 : CatNoAlmostSimpleZ2 (alternatingGroup (Fin 7))
  catM10 : CatM10AlmostSimple
  catE16 : HSStd.Zassenhaus.CatE16
  kgHS3 : HSStd.Zassenhaus.KGHS3
  kgA6Sq : HSStd.Zassenhaus.PartA.KGA6Sq
  ds81Lemma210Two : TwoB.DS81Lemma210Two

structure AlternatingStandardFormInputs : Prop where
  altStdFormBigStd : CFSG.OddStandard.AltStdSec.AltStdFormBigStd

structure CharTwoLieStandardFormInputs : Prop where
  thm54 : Induction.CITPart2 → Induction.CTEvenResidualStatement →
    Induction.Sol78Thm54ReachHered

structure HNRecognitionInputs : Prop where
  haradaHN : TwoHS.HaradaHNRecognitionKP

structure ComponentTheoryLiterature : Prop where
  fs79thm13 : Induction.FS79Thm13UseHered

structure Solomon78StandardFormLiterature : Prop where
  thm46 : Induction.CITPart2 → Induction.ChildL34WHered → Induction.ChildHeWHered →
    Induction.CTEvenResidualStatement → Induction.CTEvenSmallLieStatement →
    Induction.Sol78Thm46FSHered
  thm412 : Induction.CITPart2 → Induction.CTEvenResidualStatement →
    Induction.CTEvenSmallLieStatement → Induction.Sol78Thm412FSHered

structure FischerThompsonRowInputs : Prop where
  hypOneFi24 :
    CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.HypothesisOne (Carrier .Fi24Prime)
  fi22Covers : Induction.Fi.Fi22CoversFixesElem
  u62Covers : Induction.Fi.U62CoversFixesElem
  u62OddExcl : Induction.CITPart2 → Induction.Fi.U62OddExclHered
  thSylowWreathPair : ThStd.ThSylowWreathPair

structure TwoFi22RecognitionInputs : Prop where
  fi24Local : TwoFi22.DS81.Fi24RecognitionLocal

structure OddStandardL34HeChildren : Prop where
  l34 : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels →
    CFSG.ComponentClassification.UFrontier.GH74ModelsInput → Induction.ChildL34WHered
  he : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels →
    Induction.ChildHeWHered

section Certified

theorem sol78LitCore_of_yardstones (hCIT : Induction.CITPart2)
    (hChL34 : Induction.ChildL34WHered) (hChHe : Induction.ChildHeWHered)
    (hCTE : Induction.CTEvenResidualStatement) (hSmall : Induction.CTEvenSmallLieStatement)
    (h12 : ComponentTheoryLiterature) (h13 : Solomon78StandardFormLiterature) :
    Induction.Sol78LitCore where
  bthm := Induction.bthm_of_uhered
  fs79lemma15 := Induction.fs79Lemma15At_of_uhered
  thm24_1 := Induction.sol78Thm24_1Use_of_citPart2 hCIT
  lemma25 := Finkelstein77.Lemma25HProof.asc76Lemma25_of_hallQ8Residual
    CFSG.ComponentClassification.Foote5.HallGen.hallQ8Residual
  thm24_3 := fun _ hs' => Induction.Hyp.thm24ThreeUse_holds hs'
  thm24_3Simple := Induction.Hyp.thm24ThreeSimpleInputs_proved
  thm46 := h13.thm46 hCIT hChL34 hChHe hCTE hSmall
  thm412 := h13.thm412 hCIT hCTE hSmall
  hyp12Lie := Induction.Hyp12Lie.sol78Hyp12LieHered_holds_of_rankTwo
    (Induction.sol78Thm24_1Use_of_citPart2 hCIT)
  fs79thm13 := h12.fs79thm13

end Certified

end CFSG.Yardstones.M1442643da6f2
