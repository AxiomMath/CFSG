module

public import CFSG.Sporadic.HNOddCore.SixC
import Certificates.Kernel.HN27600.Pow4

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNOddCore in
theorem certificate27600 :     ∀ y : C6, y ∈ Dsub.comap phi6 → y ^ 4 = t6C → False :=
  KernelHN27600.pow4_facts

end Certificates
