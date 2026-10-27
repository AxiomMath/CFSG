module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
import Certificates.Kernel.LocalComp.M12Cent.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.M12Cover in
theorem certificate10023 :
    (checkK1 = true)
    ∧ (checkK3 = true)
    ∧ (checkQ2 = true)
    ∧ (checkQ4 = true)
    ∧ (checkQ5 = true) := KernelLC.M12Cent.facts

end Certificates
