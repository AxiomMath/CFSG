module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafBasic
import Certificates.Kernel.Q16J2.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate320303 : CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.NoQ16Q16
    ↥CFSG.ComponentClassification.J2Cover.sylowS :=
  KernelQ16J2.q16J2_noQ16Q16

end Certificates
