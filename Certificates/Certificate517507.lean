module

public import Certificates.Data.AE6CertF
import Certificates.Kernel.AE6F.Final

public section

namespace Certificates

open CertificateChecks

open Certificates.AE6Model in
theorem certificate517507 : fBasic () = true ∧ fTwinChecks () = true ∧ fCycChecks () = true ∧
    fDiagChecks () = true := KernelAE6F.cert517507

end Certificates
