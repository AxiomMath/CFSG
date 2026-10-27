module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3M24Inputs
public meta import CFSG.HardMathSupport.Solomon.Coordinator.GFR3M24Inputs
import Certificates.Kernel.GFR3.M24Facts
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Core
public meta import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public meta import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator in
theorem certificate13508 : m24ThreeCheck () = true := KernelGFR3.M24.m24_ok

end Certificates
