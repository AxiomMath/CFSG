module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeADenseInputs
import Certificates.Kernel.KDenseP.DenseAlign

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups.Y443Native CFSG.HardMathSupport.Dickson.I271.TabMThreeA in
theorem certificate17594 : denseAlignCheck (aV ()) = true ∧ denseAlignCheck (CFSG.YGroups.Y443Native.bV ()) = true ∧
    denseAlignCheck (wV ()) = true := KernelKDenseP.DenseAlign.denseAlign_abw

end Certificates
