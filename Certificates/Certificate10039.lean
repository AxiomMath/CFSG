module

public import Certificates.Kernel.Co1M.U45W

public section

namespace Certificates

open CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1.Module.Odd in
theorem certificate10039 :
    ∃ W : OddW, ∃ U : UW, OddOK W ∧ UOK W 2 U := ⟨w73, u39, ok73, u39_ok⟩

end Certificates
