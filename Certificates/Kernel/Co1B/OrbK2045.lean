module

public import Certificates.Kernel.Co1B.Orb2045
public import Certificates.Kernel.Co1B.TriD2045
public import Certificates.Data.Kernel.Spor.Prim
public meta import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Tri2045

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

@[expose] noncomputable def wchk (i : Nat) : Bool :=
  bAnd(allN (2 + i) (fun j => permOK 1365 11 (mask 11) (1365 * 11) (RO.S j) (RO.SI j)),
    wordEqK 1365 11 (mask 11) (pidn 1365 11) RO.S RO.SI (2 + i)
      (CFSG.Sporadic.Co1Block.twoBChainWords.getD i []) (RO.S (2 + i)))

end CertificateChecks.KernelCo1B.Tri2045

#kc_slices CertificateChecks.KernelCo1B.Tri2045.WK CertificateChecks.KernelCo1B.Tri2045.wchk 4

namespace CertificateChecks.KernelCo1B.Tri2045

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

theorem kP6 : allN 6 (fun j => permOK 1365 11 (mask 11) (1365 * 11) (RO.S j) (RO.SI j)) = true :=
  by quickRfl
theorem kS0 : Nat.beq (RO.S 0) (TB.P 10) = true := by quickRfl
theorem kS1 : Nat.beq (RO.S 1) (TB.P 11) = true := by quickRfl
theorem kB0 : Nat.beq (pg 11 (mask 11) RO.BP 0) 0 = true := by quickRfl
theorem kB1 : Nat.beq (pg 11 (mask 11) RO.BP 1) 1 = true := by quickRfl
theorem kB2 : Nat.beq (pg 11 (mask 11) RO.BP 2) 2 = true := by quickRfl
theorem kR0 : Nat.beq (rcnt (RO.LR 0)) 1365 = true := by quickRfl
theorem kR1 : Nat.beq (rcnt (RO.LR 1)) 1024 = true := by quickRfl
theorem kR2 : Nat.beq (rcnt (RO.LR 2)) 180 = true := by quickRfl

end CertificateChecks.KernelCo1B.Tri2045

end
