module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCUniqSADefs
import Certificates.Kernel.OmegaEight.Bridge3560
import Certificates.Kernel.OmegaEight.Uniq3560P
import Certificates.Kernel.OmegaEight.Uniq3560M
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCUniqWDefs
import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.Census.SiftSound
import CFSG.Certificates.Kernel.O8NodeSound
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
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitDefs
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitWit
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCUniqSA
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Wit
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.SmallOddCore.CheckSpec
import CFSG.Sporadic.Th.F2Spec
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace Certificates

open CertificateChecks.KernelO8 in
open CFSG.EvenSmallLie CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.SplitC in
theorem certificate3560 : (∃ W : UniqWit, W.J = 38 ∧ W.y = yIdx ∧ W.cl = (fun i => (invW i).1) ∧
      uniqCheckW 8192 commP CFSG.EvenSmallLie.OmegaEight.SplitC.conjP CFSG.EvenSmallLie.OmegaEight.SplitC.invP W = true)
    ∧ (∃ W : UniqWit, W.J = 36 ∧ W.y = OmegaEightMinus.yIdx ∧
      W.cl = (fun i => (OmegaEightMinus.invW i).1) ∧
      uniqCheckW 8192 OmegaEightMinus.commM OmegaEightMinus.conjM OmegaEightMinus.invM W = true) :=
  ⟨⟨wUP, rfl, rfl, rfl, uniqP⟩, ⟨wUM, rfl, rfl, rfl, uniqM⟩⟩

end Certificates
