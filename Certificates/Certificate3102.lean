module

public import CFSG.Monster.B.Dyadic.Facts
import Certificates.Kernel.BabyMonster.Facts3102

public section

namespace Certificates

open CertificateChecks

theorem certificate3102 : CFSG.Monster.B.Dyadic.Fact3102 :=
  KernelBM.Dy.fact3102_of

end Certificates
