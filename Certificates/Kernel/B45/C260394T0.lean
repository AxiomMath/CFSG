module

public import Certificates.Kernel.B45.C260394G
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelB45.C260394

theorem invOK : invB = true := by quickRfl

theorem k495 : (Nat.beq (K0 495) 0 && Nat.beq (K1 495) 1) = true := by quickRfl

end CertificateChecks.KernelB45.C260394

#kon_slices CertificateChecks.KernelB45.C260394.rowB 0 11

end
