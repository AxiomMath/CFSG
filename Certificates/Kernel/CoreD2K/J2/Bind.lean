module

public import Certificates.Kernel.CoreD2K.J2.Data
public import Certificates.Kernel.Sporadic.OddCore.J2PChain

public section

namespace CertificateChecks.KernelCoreD2K.J2

open CertificateChecks.KernelSpor

theorem gp0_eq : Nat.beq (GP 0) (J2P.S 0) = true := by decide +kernel
theorem gp1_eq : Nat.beq (GP 1) (J2P.S 1) = true := by decide +kernel

end CertificateChecks.KernelCoreD2K.J2

end
