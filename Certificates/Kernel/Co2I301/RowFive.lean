module

public import Certificates.Data.Kernel.Co2I301.SixCent
public import Certificates.Kernel.Co2I301.SixData
public import Certificates.Kernel.SporSch.Co2M.SixChain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2I301

open CFSG.KC.Enum CFSG.KC.Co2I301 CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def XC : Nat := cp SX.fk1 SX.fk2

@[expose] noncomputable def coordX (x : Nat) : Nat :=
  xb6 (nat_lit 1) (nat_lit 34) (nat_lit 9) (nat_lit 14) (nat_lit 17) (nat_lit 33) x

@[expose] noncomputable def formX (u v : Nat) : Nat :=
  formJ (nat_lit 54) (nat_lit 21) (nat_lit 59) (nat_lit 52) (nat_lit 47) (nat_lit 29) u v

theorem cent5_ok : sixCentK formX coordX (SX.pi.getD 0 0) (SX.pi.getD 1 0) XC SX.fd (nat_lit 1)
    (nat_lit 17) (nat_lit 33) (nat_lit 48) = true := by
  quickRfl

theorem inv5_ok : (inv63 XC (cp XC (cp XC (cp XC XC))) && inv63 SX.fd (cp SX.fd SX.fd)) = true := by
  quickRfl

@[expose] noncomputable def X8 : Nat := pmk (nat_lit 63) (nat_lit 8) fun i => pt XC i

theorem x8_ok : allN 63 (fun i => Nat.beq (pg 8 (CFSG.KS.mask 8) X8 i) (pt XC i) &&
    Nat.blt (pg 8 (CFSG.KS.mask 8) X8 i) 63) = true := by
  quickRfl

theorem sift5_ok : siftK 63 8 (CFSG.KS.mask 8) (63 * 8) (pidn 63 8) KernelSporSch.Co2Six.LR
    KernelSporSch.Co2Six.TRI KernelSporSch.Co2Six.BP 6 0 X8 = true := by
  quickRfl

end CertificateChecks.KernelCo2I301

end
