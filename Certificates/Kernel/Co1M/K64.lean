module

public import Certificates.Kernel.Co1M.D10064
public import Certificates.Data.Kernel.Co1M.InvFam
public import Certificates.Data.Kernel.Co1M.TwoBK
public import Certificates.Data.Kernel.Co1M.Syl64
public import Certificates.Kernel.VecCert.Co1.Data
public import CFSG.Certificates.Kernel.Co1M.OrbitMem
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.InvFam CFSG.KC.SortTree CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT
  CFSG.KC.Co1M CFSG.KC.VecK CFSG.KC.XorSel CFSG.KC.Syl64

theorem k64_l0 : chunksK (actV RST64 [0, 1, 2, 3, 4]) 5 11813081 (recT l0L64 6 42) 4096 24 3 12 64
    0 64 = true := by quickRfl

theorem k64_l1 : chunksK (actV RST64 [10, 11, 12, 13]) 4 4 (recT l1L64 6 35) 64 24 3 6 64 0 1 =
    true := by quickRfl

theorem k64_cn : allN 5 (fun k => Nat.beq (Nat.xor (getL 0 RS64 k) (idF 24))
    (selK E64 (getL 0 CN64 k))) = true := by quickRfl

theorem k64_cm0 : selAllK E64 (mulL E64 (Nat.xor (getL 0 RS64 0) (idF 24))) (CM64.getD 0 []) =
    true := by quickRfl

theorem k64_cm1 : selAllK E64 (mulL E64 (Nat.xor (getL 0 RS64 1) (idF 24))) (CM64.getD 1 []) =
    true := by quickRfl

theorem k64_cm2 : selAllK E64 (mulL E64 (Nat.xor (getL 0 RS64 2) (idF 24))) (CM64.getD 2 []) =
    true := by quickRfl

theorem k64_cm3 : selAllK E64 (mulL E64 (Nat.xor (getL 0 RS64 3) (idF 24))) (CM64.getD 3 []) =
    true := by quickRfl

theorem k64_cm4 : selAllK E64 (mulL E64 (Nat.xor (getL 0 RS64 4) (idF 24))) (CM64.getD 4 []) =
    true := by quickRfl

theorem k64_cl : selAllK E64 L64 CL64 = true := by quickRfl

theorem k64_clg : selAllK (conjL (getL 0 R64 23) (getL 0 R64 24) E64) L64 CLG64 = true := by
  quickRfl

theorem k64_cp : selAllK (E64 ++ conjL (getL 0 R64 23) (getL 0 R64 24) E64) PP64 CP64 = true := by
  quickRfl

theorem k64_piv : andB (pivOK 576 L64 PVL64) (pivOK 576 PP64 PVP64) = true := by quickRfl

theorem k64_len : Nat.ble (Nat.add (lenL E64) (lenL E64)) (Nat.add (lenL PP64) (lenL L64)) =
    true := by quickRfl

theorem k64_wit : witK (orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17) L64 U64 =
    true := by quickRfl

end CertificateChecks.KernelCo1M

end
