module

public import Certificates.Data.CFSGNative.MultRes.Witnesses
import Certificates.Kernel.LocalComp.Co2Ops

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.Co2Ops

open CFSG.SectionRank.Native in
theorem certificate14991 : ((ops2 22).cubicCheck co2MultData = true) :=
  CFSG.KC.LocalComp.Cub.cubicCheck_of_K SA.bind SB.bind
    ((rfl : co2MultData.seedA = CFSG.Sporadic.Co2.Native.seedA).trans SA.eq)
    ((rfl : co2MultData.seedB = CFSG.Sporadic.Co2.Native.seedB).trans SB.eq) cub_K

end Certificates
