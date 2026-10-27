module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQData
public import Certificates.Data.Kernel.BabyMonster.CTIB.CosetQ
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB

open CFSG.KC.BM CFSG.KC.BM.CosetQ

theorem cq6_setup : setupOK LOq AH6 6 Bs6 T6 = true := by quickRfl

theorem cq6_v : ∀ j < 1024, vOK LOq AH6 4194304 6 Bs6 T6 VT6 PT6 529 j = true := by lc_cover 64

theorem cq6_pt : ∀ p < 529, ptOK LOq AH6 4194304 6 Bs6 T6 PT6 p = true := by lc_cover 32

theorem cq6_clos : ∀ q < 7935, closOK LOq AH6 6 Bs6 T6 VT6 PT6 Gs Ds 0 q = true := by lc_cover 64

theorem cq6_d : ∀ t < 15, dOK LOq AH6 (nthN Gs t) (nthN Ds t) = true := by lc_cover 15

theorem cq6_tr : ∀ q < 529, trOK LOq AH6 6 Bs6 T6 VT6 PT6 TR6 RT6 529 Gs Ds 0 q = true := by
  lc_cover 64

theorem cq6_neg_tr : notB (trOK LOq AH6 6 Bs6 T6 VT6 PT6 TRb6 RT6 529 Gs Ds 0 2) = true := by
  quickRfl

theorem cq6_agg : andB (Nat.beq (cntV VT6 1024) 528) (incOK PT6 529) = true := by quickRfl

theorem cq6_neg_agg : notB (andB (Nat.beq (cntV VTb6 1024) 528) (incOK PT6 529)) = true := by
  quickRfl

theorem cq6_neg_setup : notB (setupOK LOq AH6 6 Bs6 (Nat.xor T6 1)) = true := by quickRfl

theorem cq6_neg_v : notB (vOK LOq AH6 4194304 6 Bs6 T6 VTb6 PT6 529 0) = true := by quickRfl

theorem cq6_neg_pt : notB (ptOK LOq AH6 4194304 6 Bs6 T6 PTr6 0) = true := by quickRfl

theorem cq6_neg_clos : notB (closOK LOq AH6 6 Bs6 T6 VT6 PTb6 Gs Ds 0 0) = true := by quickRfl

theorem cq6_neg_d : notB (dOK LOq AH6 (nthN Gs 0) (Nat.xor (nthN Ds 0) 1)) = true := by quickRfl

end CertificateChecks.KernelBM.CTIB

end
