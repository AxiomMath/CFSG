module

public import Certificates.Kernel.Co1M.Regs10071
public import Certificates.Kernel.Co1M.Data10071
public import Certificates.Data.Kernel.Co1FixList
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KC.Co1Fix CFSG.KD.Co1M CFSG.KLie.CT

theorem w71_fix : fixK 24 (trK 24 (getL 0 cmRP71 27)) 0 FR3 YR3 16 65536 0 = true := by quickRfl

theorem w71_one :
    fixListK (trK 24 (getL 0 cmRP71 27)) (trK 24 (getL 0 cmRP71 73)) FR3 W1L = true := by quickRfl

theorem w71_two :
    fixListK (trK 24 (getL 0 cmRP71 27)) (trK 24 (getL 0 cmRP71 76)) FR3 W2L = true := by quickRfl

theorem w71_neg :
    (!fixListK (trK 24 (getL 0 cmRP71 27)) (trK 24 (getL 0 cmRP71 73)) FR3 W1L.tail &&
      !fixK 24 (trK 24 (getL 0 cmRP71 27)) 0 (1 :: FR3.tail) YR3 16 65536 0) = true := by quickRfl

end CertificateChecks.KernelCo1M

end
