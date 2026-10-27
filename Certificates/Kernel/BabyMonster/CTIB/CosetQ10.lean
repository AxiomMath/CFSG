module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQData
public import Certificates.Data.Kernel.BabyMonster.CTIB.CosetQ
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB

open CFSG.KC.BM CFSG.KC.BM.CosetQ

theorem cq10_setup : setupOK LOq AH10 10 Bs10 T10 = true := by quickRfl

theorem cq10_v : ∀ j < 4, vOK LOq AH10 4194304 10 Bs10 T10 VT10 PT10 3 j = true := by lc_cover 4

theorem cq10_pt : ∀ p < 3, ptOK LOq AH10 4194304 10 Bs10 T10 PT10 p = true := by lc_cover 1

theorem cq10_clos : ∀ q < 45, closOK LOq AH10 10 Bs10 T10 VT10 PT10 Gs Ds 30 q = true := by
  lc_cover 45

theorem cq10_d : ∀ t < 15, dOK LOq AH10 (nthN Gs (30 + t)) (nthN Ds (30 + t)) = true := by
  lc_cover 15

theorem cq10_tr : ∀ q < 3, trOK LOq AH10 10 Bs10 T10 VT10 PT10 TR10 RT10 3 Gs Ds 30 q = true := by
  lc_cover 3

theorem cq10_neg_tr : notB (trOK LOq AH10 10 Bs10 T10 VT10 PT10 TRb10 RT10 3 Gs Ds 30 1) = true := by
  quickRfl

theorem cq10_agg : andB (Nat.beq (cntV VT10 4) 3) (incOK PT10 3) = true := by quickRfl

theorem cq10_neg_agg : notB (andB (Nat.beq (cntV VTb10 4) 3) (incOK PT10 3)) = true := by
  quickRfl

theorem cq10_neg_setup : notB (setupOK LOq AH10 10 Bs10 (Nat.xor T10 1)) = true := by quickRfl

theorem cq10_neg_v : notB (vOK LOq AH10 4194304 10 Bs10 T10 VTb10 PT10 3 0) = true := by quickRfl

theorem cq10_neg_pt : notB (ptOK LOq AH10 4194304 10 Bs10 T10 PTr10 0) = true := by quickRfl

theorem cq10_neg_clos : notB (closOK LOq AH10 10 Bs10 T10 VT10 PTb10 Gs Ds 30 2) = true := by
  quickRfl

theorem cq10_neg_d : notB (dOK LOq AH10 (nthN Gs 30) (Nat.xor (nthN Ds 30) 1)) = true := by
  quickRfl

end CertificateChecks.KernelBM.CTIB

end
