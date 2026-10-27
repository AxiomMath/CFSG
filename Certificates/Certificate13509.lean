module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3J2Inputs
public meta import CFSG.HardMathSupport.Solomon.Coordinator.GFR3J2Inputs
import Certificates.Kernel.GFR3.J2Facts
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

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator in
theorem certificate13509 : j2ThreeCheck () = true := KernelGFR3.J2.j2_ok

end Certificates
