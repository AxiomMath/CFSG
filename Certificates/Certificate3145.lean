module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerNativeInputs
import Certificates.Kernel.UnitarySix.FischerBase

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.Fischer in
theorem certificate3145 : (swapOK = true)
    ∧ (fixOK = true) := KernelU6.cert3145

end Certificates
