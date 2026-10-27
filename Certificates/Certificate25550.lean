module

public import CFSG.Sporadic.HNOddCore.SixC
import Certificates.Kernel.HN25550.Sign

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNOddCore in
theorem certificate25550 :     (∀ g : C6, g ∉ Dsub.comap phi6 → g ^ 2 = t6C → False) ∧
      ∃ x : C6, x ∈ Dsub.comap phi6 ∧ x ^ 2 = t6C :=
  KernelHN25550.sign_facts

end Certificates
