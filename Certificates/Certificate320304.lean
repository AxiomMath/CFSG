module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafBasic
import Certificates.Kernel.Q16J3.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate320304 : CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.NoQ16Q16 ↥CFSG.Sporadic.SmallOddCore.j3S :=
  KernelQ16J3.q16J3_noQ16Q16

end Certificates
