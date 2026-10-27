module

public import Certificates.Data.AE6CertC2
import Certificates.Kernel.AE6C2.Final

public section

namespace Certificates

open CertificateChecks

open Certificates.AE6Model in
theorem certificate517506 : c2Basic () = true ∧ c2Search () = true :=
  ⟨KernelAE6C2.c2Basic_k, KernelAE6C2.c2Search_k⟩

end Certificates
