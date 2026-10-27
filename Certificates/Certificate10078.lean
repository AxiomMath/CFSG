module

public import CFSG.Sporadic.Co1.Module.U6OddLitInputs
import Certificates.Kernel.Co1M.W78

public section

namespace Certificates

open CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1.Module.U6Odd in
theorem certificate10078 :
    ∃ W : U6W, U6OK W := ⟨w78, ok78⟩

end Certificates
