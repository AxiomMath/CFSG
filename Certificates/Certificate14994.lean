module

public import Certificates.Data.CFSGNative.MultRes.Witnesses
import Certificates.Kernel.LocalComp.Co3Ops

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.Co3Ops

open CFSG.SectionRank.Native in
theorem certificate14994 : ((ops2 22).cubicCheck co3MultData = true) :=
  CFSG.KC.LocalComp.Cub.cubicCheck_of_K SA.bind SB.bind
    ((rfl : co3MultData.seedA = CFSG.Sporadic.Co3.Native.seedA).trans SA.eq)
    ((rfl : co3MultData.seedB = CFSG.Sporadic.Co3.Native.seedB).trans SB.eq) cub_K

end Certificates
