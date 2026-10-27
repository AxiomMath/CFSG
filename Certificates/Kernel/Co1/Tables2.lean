module

public import Certificates.Kernel.Co1.Chain
import Certificates.Kernel.Co2.Intro
import Certificates.Kernel.Co1.FactsC2
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Co1.Checks.Bind
import CFSG.Certificates.Kernel.Co1.Checks.C2H

public section

namespace CertificateChecks.KernelCo1

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

theorem s2 : Tab cg2 CFSG.KD.C2.selST (nat_lit 6) (nat_lit 14) (nat_lit 47104) :=
  lceOk_sound (lceOk_intro CFSG.KD.C2.sH1 CFSG.KD.C2.sH0 CFSG.KD.Co1B.bHC2 CFSG.KD.C2.sH2
    CFSG.KD.C2.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    C2facts (by quickRfl) (by quickRfl) C2cover (by quickRfl)) cg2 r2

end CertificateChecks.KernelCo1

end
