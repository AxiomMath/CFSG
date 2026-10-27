module

public import CFSG.Monster.Tri.ASegFactsCo1WInputs
import Certificates.Kernel.Co1M.C10046

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.Tri in
theorem certificate10046 :
    (wCheck = true)
    ∧ (baseCheck = true) :=
  ⟨KernelCo1M.wCheck_true, KernelCo1M.baseCheck_true⟩

end Certificates
