module

public import Certificates.Data.ONanSp48Local
import Certificates.Kernel.Sp48L.Checks
import CFSG.Certificates.Kernel.Sp48L.Sound

public section

namespace Certificates

open CertificateChecks.KernelSp48L in
open CFSG.AGLEmbedding.KFactProofs.Sp48 in
theorem certificate9536 : sp48LocalCheck = true :=
  CFSG.KC.Sp48L.sp48LocalCheck_of gens_k r1_k r2_k r3_k r4_k r5_k r6_k r7_k r8_k r9_k r10_k
    r11_k r12_k r13_k r14_k r15_k hom_k

end Certificates
