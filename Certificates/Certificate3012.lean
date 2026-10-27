module

public import CFSG.Monster.B.Dyadic.CTIBK
import Certificates.Kernel.BabyMonster.CTIB.Fusion

public section

namespace Certificates

open CertificateChecks

theorem certificate3012 : CFSG.Monster.B.Dyadic.FactFusion :=
  KernelBM.CTIB.factFusion_of

end Certificates
