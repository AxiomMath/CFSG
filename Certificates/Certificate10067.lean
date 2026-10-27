module

public import CFSG.Sporadic.Co1.Module.CoTwoLitInputs
import Certificates.Kernel.Co1M.W67

public section

namespace Certificates

open CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1.Module.CoTwo in
theorem certificate10067 :
    ∃ W : CoTwoW, CoTwoOK W := ⟨w67, ok67⟩

end Certificates
