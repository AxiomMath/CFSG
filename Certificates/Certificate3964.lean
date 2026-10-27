module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Data
import Certificates.Kernel.LocalComp.U43K

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.Child3.SelU43 in
theorem certificate3964 : (CFSG.EvenSmallLie.Child3.SelU43.tChainCheck = true)
    ∧ (autChainCheck = true)
    ∧ (sylowChainCheck = true)
    ∧ (CFSG.EvenSmallLie.Child3.SelU43.normCheck = true)
    ∧ (CFSG.EvenSmallLie.Child3.SelU43.centCheck = true)
    ∧ (CFSG.EvenSmallLie.Child3.SelU43.repsCheck = true)
    ∧ (CFSG.EvenSmallLie.Child3.SelU43.witCheck = true) := KernelLC.U43.facts3964

end Certificates
