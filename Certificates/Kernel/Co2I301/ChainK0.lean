module

public import Certificates.Kernel.Co2I301.Bind
public meta import CFSG.Sporadic.Co2I301.Inputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo2I301

@[expose] def k0D : List (List ℤ) := CFSG.Sporadic.Co2I301.k0Words.toList.drop 2

meta def k0S : Array (Array ℕ) := CFSG.Sporadic.Co2I301.k0Arrs ()

end CertificateChecks.KernelCo2I301

end

#ks_rawchain CertificateChecks.KernelCo2I301.K0 2300 12 2300 CertificateChecks.KernelCo2I301.k0S
  CFSG.Sporadic.Co2I301.k0Base 2 CertificateChecks.KernelCo2I301.k0D

public section

namespace CertificateChecks.KernelCo2I301.K0

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem bS : allN 5 (fun j => Nat.beq (S j) (CertificateChecks.KernelCo2I301.HX.F (5 + j))) =
    true := by
  quickRfl

theorem perm : allN 5 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (S j) (SI j)) = true := by
  quickRfl

theorem bget : ∀ t < 4, CFSG.Sporadic.Co2I301.k0Base[t]! = pg 12 (mask 12) BP t := by
  decide +kernel

theorem orbProd : ((List.range 4).map fun i => rcnt (LR i)).prod = 360 := by decide +kernel

theorem hNS : 2300 ≤ NS * 2300 := by decide +kernel

end CertificateChecks.KernelCo2I301.K0

end
