module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQData
public import Certificates.Data.Kernel.BabyMonster.CTIB.CosetQ
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB

open CFSG.KC.BM CFSG.KC.BM.CosetQ

theorem cqw_cts : ∀ s < 17, ctOK LOq Syms CTs s = true := by lc_cover 17

theorem cqw_syms : symsOK LOq Syms CTs = true := by quickRfl

theorem cqw_words : ∀ t < 45, wOK LOq Syms CTs Steps Gs t = true := by lc_cover 1

theorem cqw_neg_words :
    notB (Nat.beq (wordKF Syms CTs (nthLL Steps 0) (id32 22)) Gbad) = true := by quickRfl

theorem cqw_neg_rel : notB (relOK LOq (Nat.xor (nthN Gs 0) 1)) = true := by quickRfl

theorem cqw_neg_cts : notB (ctOK LOq Syms (List.cons 1 (List.tail CTs)) 0) = true := by quickRfl

end CertificateChecks.KernelBM.CTIB

end
