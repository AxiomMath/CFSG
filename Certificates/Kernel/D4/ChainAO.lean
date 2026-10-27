module

public import Certificates.Kernel.D4.ChainAD
public import Certificates.Data.Kernel.Spor.RawSch3G
public import Certificates.Data.Kernel.Spor.RawSch3F
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4.CA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] def pTS : Nat := nat_lit 65538

theorem inv : invTabK 8 (stepsAt 2457 12 S 8 BP 0) = true := by quickRfl

theorem g12 : lv12K 12 (mask 12) S SI 8 BP 0 (stepsAt 2457 12 S 8 BP 1)
    (stepsAt 2457 12 S 8 BP 2) = true := by quickRfl

theorem g23 : lv12K 12 (mask 12) S SI 8 BP 1 (stepsAt 2457 12 S 8 BP 2)
    (stepsAt 2457 12 S 8 BP 3) = true := by quickRfl

theorem g34 : lv12K 12 (mask 12) S SI 8 BP 2 (stepsAt 2457 12 S 8 BP 3)
    (stepsAt 2457 12 S 8 BP 4) = true := by quickRfl

theorem g45 : lv12K 12 (mask 12) S SI 8 BP 3 (stepsAt 2457 12 S 8 BP 4)
    (stepsAt 2457 12 S 8 BP 5) = true := by quickRfl

theorem g56 : lv12K 12 (mask 12) S SI 8 BP 4 (stepsAt 2457 12 S 8 BP 5)
    (stepsAt 2457 12 S 8 BP 6) = true := by quickRfl

theorem tsb : allN (stCnt pTS) (fun a => Nat.blt (stAt pTS a) 8) = true := by quickRfl

theorem tso : allN 2 (fun j => anyLt (stCnt pTS) (fun a => Nat.beq (stAt pTS a) j)) = true := by
  quickRfl

end CertificateChecks.KernelD4.CA

end
