module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQData
public import Certificates.Data.Kernel.BabyMonster.CTIB.CosetQ
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB

open CFSG.KC.BM CFSG.KC.BM.CosetQ

theorem cq8_setup : setupOK LOq AH8 8 Bs8 T8 = true := by quickRfl

theorem cq8_v : ∀ j < 64, vOK LOq AH8 0 8 Bs8 T8 VT8 PT8 37 j = true := by lc_cover 64

theorem cq8_pt : ∀ p < 37, ptOK LOq AH8 0 8 Bs8 T8 PT8 p = true := by lc_cover 8

theorem cq8_clos : ∀ q < 555, closOK LOq AH8 8 Bs8 T8 VT8 PT8 Gs Ds 15 q = true := by lc_cover 64

theorem cq8_d : ∀ t < 15, dOK LOq AH8 (nthN Gs (15 + t)) (nthN Ds (15 + t)) = true := by
  lc_cover 15

theorem cq8_tr : ∀ q < 37, trOK LOq AH8 8 Bs8 T8 VT8 PT8 TR8 RT8 37 Gs Ds 15 q = true := by
  lc_cover 37

theorem cq8_neg_tr : notB (trOK LOq AH8 8 Bs8 T8 VT8 PT8 TRb8 RT8 37 Gs Ds 15 2) = true := by
  quickRfl

theorem cq8_agg : andB (Nat.beq (cntV VT8 64) 36) (incOK PT8 37) = true := by quickRfl

theorem cq8_neg_agg : notB (andB (Nat.beq (cntV VTb8 64) 36) (incOK PT8 37)) = true := by
  quickRfl

theorem cq8_neg_setup : notB (setupOK LOq AH8 8 Bs8 (Nat.xor T8 1)) = true := by quickRfl

theorem cq8_neg_v : notB (vOK LOq AH8 0 8 Bs8 T8 VTb8 PT8 37 3) = true := by quickRfl

theorem cq8_neg_pt : notB (ptOK LOq AH8 0 8 Bs8 T8 PTr8 0) = true := by quickRfl

theorem cq8_neg_clos : notB (closOK LOq AH8 8 Bs8 T8 VT8 PTb8 Gs Ds 15 16) = true := by quickRfl

theorem cq8_neg_d : notB (dOK LOq AH8 (nthN Gs 15) (Nat.xor (nthN Ds 15) 1)) = true := by quickRfl

end CertificateChecks.KernelBM.CTIB

end
