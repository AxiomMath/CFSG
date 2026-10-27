module

public import Certificates.Data.SmithB45TitsTor
import Certificates.Kernel.TitsW.P260420

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.B45Tor in
theorem certificate260420 : titsTorWordsCheck = true ∧ titsTorPlaneCheck = true ∧ titsTorNormCheck = true ∧
    titsTorRelCheck = true ∧ titsTorClassCheck = true := KernelTitsW.P260420.facts

end Certificates
