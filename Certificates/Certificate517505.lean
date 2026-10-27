module

public import Certificates.Data.AE6ModelFW
import Certificates.Kernel.AE6FW.Final

public section

namespace Certificates

open CertificateChecks

open Certificates.AE6Model in
theorem certificate517505 : fwComm () = true ∧ fwInS () = true ∧ fwNorm () = true ∧ fwMeet () = true ∧
    fwFrames () = true :=
  ⟨KernelAE6FW.fwComm_k, KernelAE6FW.fwInS_k, KernelAE6FW.fwNorm_k, KernelAE6FW.fwMeet_k,
    KernelAE6FW.fwFrames_k⟩

end Certificates
