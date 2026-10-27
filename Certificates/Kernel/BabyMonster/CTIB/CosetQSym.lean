module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQData
public import Certificates.Data.Kernel.BabyMonster.CTIB.CosetQ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB

open CFSG.KC.BM CFSG.KC.BM.CosetQ

theorem cqs_rel : relOK LOq (nthN Syms 13) = true := by quickRfl

theorem cqs_inv : andB (Nat.beq (compAut LOq (nthN Syms 1) (nthN Syms 13)) (id32 22))
    (Nat.beq (compAut LOq (nthN Syms 13) (nthN Syms 1)) (id32 22)) = true := by quickRfl

theorem cqs_neg_inv : notB (Nat.beq (compAut LOq (nthN Syms 1) (nthN Syms 14)) (id32 22)) = true := by
  quickRfl

theorem cqs_neg_rel : notB (relOK LOq (Nat.xor (nthN Syms 13) 1)) = true := by quickRfl

end CertificateChecks.KernelBM.CTIB

end
