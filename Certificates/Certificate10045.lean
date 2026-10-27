module

public import Certificates.Kernel.Co1M.U45W

public section

namespace Certificates

open CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1.Module.Odd in
theorem certificate10045 :
    ∃ W : OddW, ∃ U : UW, OddOK W ∧ UOK W 1 U := ⟨w73, u45, ok73, u45_ok⟩

end Certificates
