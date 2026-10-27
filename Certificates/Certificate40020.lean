module

public import Certificates.Data.KFCub2Th
import CFSG.Certificates.Kernel.OpsF2KSound
import CFSG.Certificates.Kernel.OpsF2KQSound
import Certificates.Kernel.LocalComp.ThCub2Q

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.Th8

theorem certificate40020 : (CFSG.SectionRank.Native.ops2 248).cub2Check CFSG.SectionRank.Native.thFiveData = true :=
  CFSG.KC.OpsF2K.cub2Check_of_K SA.bind SB.bind
    ((rfl : thFiveData.seedA = CertificateChecks.KernelLC.thSeedA).trans SA.eq)
    ((rfl : thFiveData.seedB = CertificateChecks.KernelLC.thSeedB).trans SB.eq)
    (CFSG.KC.OpsF2K.cub2K_of_Q CertificateChecks.KernelLC.ThCub2.cub2_Q)

end Certificates
