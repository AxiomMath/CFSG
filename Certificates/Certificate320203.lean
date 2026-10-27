module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Q16
public import CFSG.Sporadic.Schreier.Co3Outer
import Certificates.Kernel.Q16Sp6.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate320203 : CFSG.CGT.PushingUpLit.SolKNA.R4.NoQ16 ↥CFSG.Sporadic.Schreier.Co3.co3X36 :=
  KernelQ16Sp6.q16Sp6_noQ16

end Certificates
