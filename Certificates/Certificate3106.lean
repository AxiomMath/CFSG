module

public import CFSG.Monster.B.Dyadic.Facts
import Certificates.Kernel.BabyMonster.Facts3106

public section

namespace Certificates

open CertificateChecks

theorem certificate3106 : CFSG.Monster.B.Dyadic.Fact3106 :=
  KernelBM.Dy.fact3106_of

end Certificates
