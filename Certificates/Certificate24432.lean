module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SuzInputs
public import CFSG.Sporadic.SuzOddCore.InvPerms
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rank
import Certificates.Certificate2289
import Certificates.Certificate2306
import Certificates.Kernel.Sporadic.Suz.Hyp24432Glue
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover in
open CFSG.EvenSporadicStandard.HypOne in
theorem certificate24432 : FourClassesLarge ↥(centralizerIn suzM (suzInv 0)) ∧
    FourClassesLarge ↥(centralizerIn suzM (suzInv 1)) ∧
    (∀ i < 4, FourClassesLarge ↥(centralizerIn suzT (suzInv i))) ∧ HasElemAbelianEight ↥suzM ∧
    ∀ i ∈ [2, 3], ∃ l ∈ suzM, orderOf (l * suzInv i * l⁻¹ * (suzInv i)⁻¹) = 2 :=
  ⟨KernelSpor.SuzHG.fourClassesLarge_M0, KernelSpor.SuzHG.fourClassesLarge_M1,
    KernelSpor.SuzHG.fourClassesLarge_T, KernelSpor.SuzHG.hasElemAbelianEight_suzM,
    KernelSpor.SuzHG.fours_wit⟩

end Certificates
