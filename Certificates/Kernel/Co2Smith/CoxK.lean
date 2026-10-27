module

public import Certificates.Data.Kernel.Co2Smith.Cox
public import Certificates.Kernel.Co2Smith.LettersData
public import Certificates.Kernel.Co2Smith.CoxData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

theorem tp_k : (glMkTWords.size == 15 && (List.range 15).all fun j =>
    (glMkTWords[j]!).all (· < 22) && eqK (TP j) (wK LP glMkTWords[j]!)) = true := by
  decide +kernel

theorem tab_k : ((List.range 15).all fun a => (List.range 15).all fun b =>
    tabK (TB 0) a b == (a != b && eqK (powK (mulV (TP a) (TP b)) 3) IDP) &&
      tabK (TB 1) a b == commK (TP a) (TP b)) = true := by
  decide +kernel

theorem coxConj_k : (pathK (TB 0) (TB 1) 0 1 2 3 4 && glMkCox.all fun e =>
    e.2.all (· < 22) && commK (wK LP e.2) (wK LP [0]) && conjPathK TP (wK LP e.2) e.1) = true := by
  decide +kernel

theorem coxLoop_k : coxLoopK (TB 0) (TB 1) glMkCox = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
