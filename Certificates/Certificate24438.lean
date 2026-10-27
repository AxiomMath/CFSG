module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowRows
public import CFSG.Sporadic.SmallOddCore.Co3FusionCheckInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rank
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.Co3Cert
public import CFSG.Sporadic.Schreier.Co3Outer
public import Certificates.Certificate2152
public import Certificates.Certificate2158
public import Certificates.Kernel.Sporadic.Co3.Hyp24438Glue
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

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 in
open CFSG.EvenSporadicStandard.HypOne in
theorem certificate24438 : FourClassesLarge ↥(centralizerIn co3P co3Z) ∧
    FourClassesLarge ↥(centralizerIn co3P co3Tt) ∧ HasElemAbelianEight ↥co3P :=
  ⟨KernelSpor.Co3HG.fourClassesLarge_z, KernelSpor.Co3HG.fourClassesLarge_t,
    KernelSpor.Co3HG.hasElemAbelianEight_co3P⟩

end Certificates
