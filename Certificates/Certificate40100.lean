module

public import Certificates.Data.Co1GenData
import CFSG.Certificates.Kernel.OpsF2KCo1GenSound
import Certificates.Kernel.LocalComp.Co1Gen

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.Co1Ops

theorem certificate40100 : (CFSG.SectionRank.Native.ops2 24).co1GenCheck CFSG.SectionRank.Native.Co1Gen.dataFive = true :=
  CFSG.KC.OpsF2K.co1GenCheck_of_K SA.bind SB.bind
    ((rfl : Co1Gen.dataFive.seedA = CFSG.Sporadic.Co1.Native.seedA).trans SA.eq)
    ((rfl : Co1Gen.dataFive.seedB = CFSG.Sporadic.Co1.Native.seedB).trans SB.eq)
    CertificateChecks.KernelLC.Co1Gen.gen_K

end Certificates
