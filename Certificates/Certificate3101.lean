module

public import CFSG.Monster.B.Dyadic.Facts
import Certificates.Kernel.BabyMonster.Facts3101

public section

namespace Certificates

open CertificateChecks

theorem certificate3101 : CFSG.Monster.B.Dyadic.Fact3101 :=
  KernelBM.Fix.fact3101_of

end Certificates
