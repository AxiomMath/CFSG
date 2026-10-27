module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxRest
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxD4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxM11
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxM12
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxU33
public import CFSG.CGT.T75E.Reduce
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.CGT.Timmesfeld75.Targets
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ2Pair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec
public import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Kernel.SporSch.Th.Key2311
public import Certificates.Kernel.SporSch.Th.Orb2315
public import Certificates.Kernel.SporSch.Th.Plane2320
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.Quasithin

theorem input15120CentMaxRest_holds
    : Input15120CentMaxRest :=
  input15120CentMaxRest_of_three
    (fun Q _ _ P h1 h2 h3 W hW hW0 => centMax_u33 Q P h1 h2 h3 W hW hW0)
    (fun Q _ _ P h1 h2 h3 W hW hW0 => centMax_3d4 Q P h1 h2 h3 W hW hW0)
    (fun Q _ _ P h1 h2 h3 W hW hW0 => centMax_m11 Q P h1 h2 h3 W hW hW0)
    (fun Q _ _ P h1 h2 h3 W hW hW0 => centMax_m12 Q P h1 h2 h3 W hW hW0)

end CFSG.Quasithin
