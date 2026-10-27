module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Data
import Certificates.Kernel.LocalComp.L39K

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.Child3.SelL39 in
theorem certificate3965 : (tChainCheck = true)
    ∧ (autChainCheck = true)
    ∧ (sylowChainCheck = true)
    ∧ (normCheck = true)
    ∧ (centCheck = true)
    ∧ (repsCheck = true)
    ∧ (witCheck = true) := KernelLC.L39.facts3965

end Certificates
