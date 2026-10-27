module

public import CFSG.RankThree.PartOne.S11d.ThreeClaim
public import CFSG.RankThree.PartOne.S11d.FiveClaimCore
public import CFSG.RankThree.PartOne.S11d.FinalClaim
public import CFSG.RankThree.PartOne.S11d.LieGoodAll
public import CFSG.RankThree.PartOne.S11d.OutStructure
public import CFSG.RankThree.PartOne.S11d.ThreeCompAllR
public import CFSG.RankThree.PartOne.S11d.OutPCyclicThetaClosed
public import CFSG.RankThree.PartOne.FTL.Main

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

open CFSG.Assembly (InCatalog)

open CFSG.Assembly.LowTwoRank (StatedLieTag)

open CFSG.RankThree.PartOne.TCX CFSG.RankThree.PartOne.FieldFix

theorem sec11Claims_of_allTagsR (hS : SchreierFor InCatalog) (h112 : InSec11Two)
    (hK : CatalogPrimeTwoAutomorphismsInner) (hKF : KF128Rank1)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hTE : TwoExcPair)
    (h3D4 : ThreeCompT .trialityD4) (h2F4 : ThreeCompT .twistedF4)
    (hP4a : FieldOnComponentOuter) :
    Sec11Indeed.ThreeClaim ∧ Sec11Indeed.FourClaim ∧ Sec11Indeed.FiveClaimCore ∧
      Sec11Indeed.FinalClaim := by
  have hP4b : OutPCyclicTheta := outPCyclicTheta_of_griess hGA
  have h114 : Sec11Indeed.FourClaim :=
    FTL.fourClaim_of_inputs hS h112 TCB.tauCetiCatalogBridge hK fieldAutCoset_closed
      fieldFixedPElements_closed fieldFixedCentralizer_closed fieldFixedNonLocal_closed
  have h113 : Sec11Indeed.ThreeClaim :=
    Sec11Indeed.threeClaim_of hS h112 h114
      (threeComponents_of_allTagsR hGA hTE h3D4 h2F4) hP4a hP4b
  have hcore : Sec11Indeed.FiveClaimCore :=
    Sec11Indeed.fiveClaimCore_of hS h112 hK h113 h114 lieGoodComponent_closed
      fieldFixedTwoElements_closed hP4a hP4b
  exact ⟨h113, h114, hcore,
    Sec11Indeed.finalClaim_of h112 hKF h113 h114 (Sec11Indeed.fiveClaim_of_core hS hKF hcore)
      fieldFixedPElements_closed outPCyclic⟩

end CFSG.RankThree.PartOne
