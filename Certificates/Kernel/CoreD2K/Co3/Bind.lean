module

public import Certificates.Kernel.CoreD2K.Co3.Data
public import Certificates.Kernel.Sporadic.Co3.C

public section

namespace CertificateChecks.KernelCoreD2K.Co3

open CertificateChecks.KernelSpor

theorem gp0_eq : Nat.beq (GP 0) (Co3C.S 0) = true := by decide +kernel
theorem gp1_eq : Nat.beq (GP 1) (Co3C.S 1) = true := by decide +kernel

end CertificateChecks.KernelCoreD2K.Co3

end
