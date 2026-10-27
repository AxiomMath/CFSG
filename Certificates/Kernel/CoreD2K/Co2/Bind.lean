module

public import Certificates.Kernel.CoreD2K.Co2.Data
public import Certificates.Kernel.Sporadic.Co2.ChainAD

public section

namespace CertificateChecks.KernelCoreD2K.Co2

open CertificateChecks.KernelSpor

theorem gp0_eq : Nat.beq (GP 0) (Co2A.S 0) = true := by decide +kernel
theorem gp1_eq : Nat.beq (GP 1) (Co2A.S 1) = true := by decide +kernel

end CertificateChecks.KernelCoreD2K.Co2

end
