module

public import Certificates.Kernel.Co2I301.Mats
public import Certificates.Kernel.SporSch.Co2M.EnumQ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2I301

open CFSG.KC.Enum CFSG.KS.Co2M CertificateChecks.KernelSporSch.Co2M

theorem qnc_ok : allN 512 (fun k => bIf(Nat.beq k 0, true, bIf(Nat.beq k 23, true,
    Bool.not (Nat.beq (vmK (vmK (VG (PV 0) 0) (M 1)) (CFSG.KS.Co2LE.eM QR k))
      (vmK (vmK (VG (PV 0) 0) (CFSG.KS.Co2LE.eM QR k)) (M 1)))))) = true := by
  quickRfl

end CertificateChecks.KernelCo2I301

end
