module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3RuInputs
public meta import CFSG.HardMathSupport.Solomon.Coordinator.GFR3RuInputs
import Certificates.Kernel.RuThree.ClassFacts
import CFSG.Sporadic.Schreier.RuCheckBasicInputs
import CFSG.Sporadic.Schreier.RuCheckChainsInputs
import CFSG.Sporadic.Schreier.RuArrays
import CFSG.Certificates.NativeSetOrbit
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
public import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuEnum

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator in
theorem certificate13505 : ruThreeClassCheck () = true := KernelRuThree.class_ok

end Certificates
