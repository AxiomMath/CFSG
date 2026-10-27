module

public import Certificates.Data.AE6ModelC
import Certificates.Kernel.AE6ModC.Final

public section

namespace Certificates

open CertificateChecks

open Certificates.AE6Model in
theorem certificate517502 : ae6C3 () = true ∧ ae6C1 () = true ∧ ae6C1i () = true :=
  ⟨KernelAE6ModC.ae6C3_k, KernelAE6ModC.ae6C1_k, KernelAE6ModC.ae6C1i_k⟩

end Certificates
