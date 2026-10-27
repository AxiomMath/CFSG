
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeSylowDefs
import Certificates.Kernel.OmegaEight.Bridge3002
import Certificates.Kernel.OmegaEight.SA3002K
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.Census.SiftSound
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Exceptional.E6E7
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Steinberg.G2
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverModel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylow
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeBridgeBase
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.SmallOddCore.CheckSpec
import CFSG.Sporadic.Th.F2Spec
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEightMinus in
theorem certificate3002 : (nsCheck = true)
    ∧ (omegaChainCheck = true)
    ∧ (autChainCheck = true)
    ∧ (sylowChainCheck = true)
    ∧ (structureCheck = true)
    ∧ (stabCheck = true)
    ∧ (treeLitCheck = true)
    ∧ (sylowRepsLitCheck = true)
    ∧ (cent0Check = true)
    ∧ SAFacts
    ∧ (fgCheck = true)
    ∧ (oddCheck = true)
    ∧ (invsCheck = true) := KernelO8.cert3002

end Certificates
