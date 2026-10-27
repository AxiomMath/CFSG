module

public import Certificates.Data.KFCub2Co3
import CFSG.Certificates.Kernel.OpsF2KSound
import Certificates.Kernel.LocalComp.Co3Ops

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.Co3Ops

theorem certificate40022 : (CFSG.SectionRank.Native.ops2 22).cub2Check CFSG.SectionRank.Native.co3FiveData = true :=
  CFSG.KC.OpsF2K.cub2Check_of_K SA.bind SB.bind
    ((rfl : co3FiveData.seedA = CFSG.Sporadic.Co3.Native.seedA).trans SA.eq)
    ((rfl : co3FiveData.seedB = CFSG.Sporadic.Co3.Native.seedB).trans SB.eq) cub2_K

end Certificates
