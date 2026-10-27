module

public import Certificates.Kernel.CoreD2K.RuThree.Data
public import Certificates.Kernel.Misc.RuInv.Data

public section

namespace CertificateChecks.KernelCoreD2K.RuThree

open CertificateChecks.KernelMisc.RuInv

theorem gp0_eq : Nat.beq (GP 0) AD.n0 = true := by decide +kernel
theorem gp1_eq : Nat.beq (GP 1) AD.n1 = true := by decide +kernel

end CertificateChecks.KernelCoreD2K.RuThree

end
