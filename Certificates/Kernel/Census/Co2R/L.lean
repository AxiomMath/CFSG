module

public import Certificates.Kernel.Census.Co2R.Data
public import CFSG.Certificates.Kernel.Census.ToMain
import all Certificates.Kernel.Census.Co2R.Data
import all CFSG.Certificates.Kernel.Census.ToMain
import all Certificates.Data.Kernel.Census.PackedBase
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CertificateChecks.KernelCensus.Co2R

open CFSG.KC.Census CertificateChecks.KernelSporSch

set_option maxRecDepth 1000000

theorem kInvL : invLB 12 11 L 2300 = true := by quickRfl

theorem kCanon8 : canon1 2300 12 (Co2LS.S 8) = true := by quickRfl

end CertificateChecks.KernelCensus.Co2R

end
