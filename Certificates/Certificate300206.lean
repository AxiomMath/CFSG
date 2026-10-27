module

public import CFSG.Quasithin.Background.Harris.R1.D4Q2Check
import Certificates.Kernel.D4QK.C300206

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.Background.Harris.R1.D4Vert CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2.Native in
theorem certificate300206 :
    (CFSG.LargeExtraspecial.S63.mulR y1A y1iA == oneR) = true
    ∧ (CFSG.LargeExtraspecial.S63.mulR y2A y2A == oneR) = true
    ∧ (CFSG.Sporadic.SmallF2.Native.powRows 24 CFSG.Quasithin.Background.Harris.R1.D4Vert.zA 7 == oneR) = true
    ∧ (!(CFSG.LargeExtraspecial.S63.mulR y1A y1A == oneR)) = true
    ∧ CFSG.Quasithin.Background.Harris.R1.D4Vert.relsOK (phiArr y1A oneR) (phiArr y1iA oneR) qR1 = true
    ∧ CFSG.Quasithin.Background.Harris.R1.D4Vert.relsOK (phiArr oneR y2A) (phiArr oneR y2A) qR2 = true
    ∧ CFSG.Quasithin.Background.Harris.R1.D4Vert.relsOK qGensA qGensInvA qR12 = true
    ∧ CFSG.Quasithin.Background.Harris.R1.D4Vert.tabOK qGensA qGensInvA tabQ2 2048 = true
    ∧ CFSG.Quasithin.Background.Harris.R1.D4Vert.tabOK kGens kGensInv tabKc 42 = true
    ∧ invOKT tQ = true
    ∧ CFSG.Quasithin.Background.Harris.R1.D4Vert.pairCheck tQ tK = true
    ∧ commCheck tK = true
    ∧ cubeCheck tK = true := KernelD4Q.C300206.cert

end Certificates
