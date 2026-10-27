module

public import Certificates.Kernel.AS91K468.Checks46C
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

noncomputable section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAS91K468

open Certificates.Kernel.AS91K468 CFSG.KD.AS91K46

#kc_each CertificateChecks.KernelAS91K468 ch89406_b0_ (fun i => jAll2 pfL (chunkL 20 i (fk 0))) 0 1

#kc_each CertificateChecks.KernelAS91K468 ch89406_b1_ (fun i => jAll2 pfL (chunkL 20 i (fk 1))) 0 6

#kc_each CertificateChecks.KernelAS91K468 ch89406_b2_ (fun i => jAll2 pfL (chunkL 20 i (fk 2)))
  0 19

#kc_each CertificateChecks.KernelAS91K468 ch89406_b3_ (fun i => jAll2 pfL (chunkL 20 i (fk 3))) 0 8

#kc_each CertificateChecks.KernelAS91K468 ch89406_b4_ (fun i => jAll2 pfL (chunkL 20 i (fk 4))) 0 1

theorem ch89406_b_neg : (!jFQ (pfL ++ pfL) w1M w1M) = true := by quickRfl

end CertificateChecks.KernelAS91K468

end
