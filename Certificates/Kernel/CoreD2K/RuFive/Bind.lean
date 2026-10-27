module

public import Certificates.Kernel.CoreD2K.RuFive.Data
public import Certificates.Kernel.Misc.RuInv.Data

public section

namespace CertificateChecks.KernelCoreD2K.RuFive

open CertificateChecks.KernelMisc.RuInv

theorem gp0_eq : Nat.beq (GP 0) AD.n0 = true := by decide +kernel
theorem gp1_eq : Nat.beq (GP 1) AD.n1 = true := by decide +kernel

end CertificateChecks.KernelCoreD2K.RuFive

end
