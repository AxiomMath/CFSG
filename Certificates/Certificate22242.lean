module

public import Certificates.Data.CatFactsL4U4P1L43Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LAction
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecC
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Facts
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1FbarRows
import Certificates.Certificate22240
import Certificates.Kernel.P1L43.Fbar
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecA
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecB
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82L2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Open.QuasithinDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HarrisLit.P1 CFSG.ComponentClassification.HarrisLit.P1.L43 in
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL) in
theorem certificate22242 : P1ModelFacts (projectiveSL 4 (ZMod 3)) ∧ (∀ R ∈ l43Runs, RunFacts pi.range R) ∧
    ∀ i < l43Runs.length, ∀ r ∈ (l43Runs.getD i default).rows, FbarRowFacts pi.range (i == 0) r :=
  ⟨KernelP1L43.l43_p1ModelFacts, KernelP1L43.l43_runFacts, KernelP1L43.l43_fbarRows⟩

end Certificates
