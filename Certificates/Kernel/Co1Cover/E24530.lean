module

public import Certificates.Kernel.Co1Cover.Data
public import Certificates.Kernel.Co1Cover.EData
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Co1FixListS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1Cover.ECore

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CertificateChecks.KernelCo1Cover

theorem eA_ok : Nat.beq (eprodK E 3) EAP = true := by quickRfl

theorem eC_ok : Nat.beq (eprodK E 1) ECP = true := by quickRfl

theorem eA_order : orderIsK 24 EAP 2 = true := by quickRfl

theorem eC_order : orderIsK 24 ECP 2 = true := by quickRfl

theorem trA_ok : Nat.beq (trK 24 EAP) EAtP = true := by quickRfl

theorem trC_ok : Nat.beq (trK 24 ECP) ECtP = true := by quickRfl

theorem fixA_q0 : Nat.beq (qCountK 24 QtP (FA.drop 2) (nat_lit 0)) 7680 = true := by
  quickRfl

theorem fixA_q1 : Nat.beq (qCountK 24 QtP (FA.drop 2) (Nat.xor (nat_lit 0) (FA.getD 1 0))) 7680 = true := by
  quickRfl

theorem fixA_q2 : Nat.beq (qCountK 24 QtP (FA.drop 2) (Nat.xor (nat_lit 0) (FA.getD 0 0))) 7680 = true := by
  quickRfl

theorem fixA_q3 : Nat.beq (qCountK 24 QtP (FA.drop 2) (Nat.xor (Nat.xor (nat_lit 0) (FA.getD 0 0)) (FA.getD 1 0))) 7680 = true := by
  quickRfl

theorem fixA_ok : fixK 24 EAtP QtP FA YA 16 65536 30720 = true := by
  unfold CFSG.KC.Co1F2.fixK
  rw [CFSG.KC.Co1Fix.qCountK_split2 24 QtP (nat_lit 0) FA (Nat.le_of_ble_eq_true (by quickRfl)),
    Nat.eq_of_beq_eq_true fixA_q0, Nat.eq_of_beq_eq_true fixA_q1, Nat.eq_of_beq_eq_true fixA_q2,
    Nat.eq_of_beq_eq_true fixA_q3]
  quickRfl

theorem fixC_ok : fixK 24 ECtP QtP FC YC 12 4096 2048 = true := by quickRfl

end CertificateChecks.KernelCo1Cover.ECore

end
