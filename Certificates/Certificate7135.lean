module

public import Certificates.Data.Antiflag
import Certificates.Kernel.Antiflag.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate7135 : Antiflag.Facts 4 ∧ Antiflag.Facts 5 :=
  ⟨KernelAntiflag.facts4, KernelAntiflag.facts5⟩

end Certificates
