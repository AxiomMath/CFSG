module

public import CFSG.Sporadic.Co1.Module.Co2StabLitInputs
import Certificates.Kernel.Co1M.W64

public section

namespace Certificates

open CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1.Module.Co2Stab in
theorem certificate10064 :
    ∃ W : SylW, SylOK W := ⟨w64, ok64⟩

end Certificates
