module

public import Certificates.Kernel.Co1.Chain
import Certificates.Kernel.Co2.Intro
import Certificates.Kernel.Co1.FactsC1
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Co1.Checks.Bind
import CFSG.Certificates.Kernel.Co1.Checks.C1H

public section

namespace CertificateChecks.KernelCo1

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

theorem s1 : Tab g0 CFSG.KD.C1.selST (nat_lit 7) (nat_lit 16) (nat_lit 98280) :=
  lceOk_sound (lceOk_intro CFSG.KD.C1.sH1 CFSG.KD.C1.sH0 CFSG.KD.Co1B.bHC1 CFSG.KD.C1.sH2
    CFSG.KD.C1.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    C1facts (by quickRfl) (by quickRfl) C1cover (by quickRfl)) g0 r1

end CertificateChecks.KernelCo1

end
