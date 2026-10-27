module

public import Certificates.Data.KFCub2Co2
import CFSG.Certificates.Kernel.OpsF2KSound
import Certificates.Kernel.LocalComp.Co2Ops

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.Co2Ops

theorem certificate40021 : (CFSG.SectionRank.Native.ops2 22).cub2Check CFSG.SectionRank.Native.co2FiveData = true :=
  CFSG.KC.OpsF2K.cub2Check_of_K SA.bind SB.bind
    ((rfl : co2FiveData.seedA = CFSG.Sporadic.Co2.Native.seedA).trans SA.eq)
    ((rfl : co2FiveData.seedB = CFSG.Sporadic.Co2.Native.seedB).trans SB.eq) cub2_K

end Certificates
