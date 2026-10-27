module

public import Certificates.Data.CFSGNative.MultRes.Witnesses
import CFSG.Certificates.Kernel.OpsF2KSqSound
import Certificates.Kernel.LocalComp.Co1Ops

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.Co1Ops

open CFSG.SectionRank.Native in
theorem certificate14996 : ((ops2 24).squareCheck co1MultData = true) :=
  CFSG.KC.OpsF2K.squareCheck_of_K SA.bind SB.bind
    ((rfl : co1MultData.seedA = CFSG.Sporadic.Co1.Native.seedA).trans SA.eq)
    ((rfl : co1MultData.seedB = CFSG.Sporadic.Co1.Native.seedB).trans SB.eq) sq_K

end Certificates
