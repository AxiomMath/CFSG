module

public import Certificates.Data.J3Sylow
import CFSG.Certificates.Kernel.OpsF2KEnumSound
import Certificates.Kernel.LocalComp.J3Enum

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.J3Ops

open CFSG.SectionRank.Native in
theorem certificate452000 : (ops2 80).sylowCentralCheck j3SylowCentralData = true :=
  CFSG.KC.OpsF2K.sylowCentralCheck_of_K SA.bind SB.bind
    ((rfl : j3SylowCentralData.seedA = CFSG.Sporadic.J3.Native.seedA).trans SA.eq)
    ((rfl : j3SylowCentralData.seedB = CFSG.Sporadic.J3.Native.seedB).trans SB.eq)
    CertificateChecks.KernelLC.J3Enum.sylow_K

end Certificates
