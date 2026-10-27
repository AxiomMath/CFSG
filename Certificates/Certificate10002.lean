module

public import Certificates.Kernel.S12Tri.Checks

public section

namespace Certificates

open CertificateChecks

open CFSG.LargeExtraspecial.S12Tri in
theorem certificate10002 :
    (a6Check = true)
    ∧ (a5Check = true) :=
  ⟨KernelS12Tri.a6Check_true, KernelS12Tri.a5Check_true⟩

end Certificates
