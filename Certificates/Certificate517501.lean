module

public import Certificates.Kernel.AE6Core.Final

public section

namespace Certificates

open CertificateChecks

open Certificates.AE6Model in
theorem certificate517501 : ae6Gens () = true ∧ ae6CComm () = true ∧ ae6CChains () = true :=
  ⟨KernelAE6Core.gens_ok, KernelAE6Core.comm_ok, KernelAE6Core.chains_ok⟩

end Certificates
