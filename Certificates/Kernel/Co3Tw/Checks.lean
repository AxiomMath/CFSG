module

public import Certificates.Kernel.Co3Tw.Enum
public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Data.Kernel.Co3Tw
public import Certificates.Data.Kernel.Misc.PermWit

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelCo3Tw

open CFSG.KC.Enum CFSG.KS CFSG.KC.Co3Tw CFSG.KC.PermWit

theorem szP : Nat.beq EP.ng 6 = true ∧ Nat.beq EP.N 2187 = true :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem pGP : allN 6 (fun k => CFSG.KC.Misc.ArrEnum.permB 276 9 (EP.G k)) = true := by
  decide +kernel

theorem siftP : allN 6 (fun k => siftR 276 9 CertificateChecks.KernelSpor.Co3C.LR
    CertificateChecks.KernelSpor.Co3C.TRI CertificateChecks.KernelSpor.Co3C.BP 7 (EP.G k)) = true := by
  decide +kernel

theorem o3P : Nat.beq (cntO3 2187 EP.T) 890 = true := by
  decide +kernel

end CertificateChecks.KernelCo3Tw

end
