module

public import CFSG.Sporadic.Co1.Module.CoTwoAutLitInputs
import Certificates.Kernel.Co1M.W66

public section

namespace Certificates

open CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1.Module.CoTwoAut in
theorem certificate10066 :
    ∃ D : AutW, AutOK D := ⟨w66, ok66⟩

end Certificates
