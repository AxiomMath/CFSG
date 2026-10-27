module

public import CFSG.Sporadic.Co1.Module.CoTwoAutGraphLitInputs
import Certificates.Kernel.Co1M.W65

public section

namespace Certificates

open CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1.Module.CoTwoAut in
theorem certificate10065 :
    ∃ W : GraphW, GraphOK W := ⟨w65, ok65⟩

end Certificates
