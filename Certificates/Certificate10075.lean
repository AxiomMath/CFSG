
module


public import CFSG.Sporadic.Co1.Module.OrbitsInputs
import Certificates.Kernel.Co1M.C10075

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1.Module in
theorem certificate10075 :
    (orbitCheck 2 98280 [4096, 1] = true)
    ∧ (orbitCheck 4096 8386560 [1] = true)
    ∧ (orbitCheck 1 8292375 [] = true) :=
  ⟨KernelCo1M.orbitCheck_v₂_k, KernelCo1M.checks_k.1, KernelCo1M.checks_k.2⟩

end Certificates
