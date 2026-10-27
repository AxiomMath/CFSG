module

public import Certificates.Data.WCSporRot
import CFSG.Certificates.Kernel.OpsF2KSqSound
import CFSG.Certificates.Kernel.OpsF2KSqQSound
import Certificates.Kernel.LocalComp.ThSqQ

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.Th8

open CFSG.SectionRank.Native in
theorem certificate41506 : (ops2 248).squareCheck thSevenRot = true :=
  CFSG.KC.OpsF2K.squareCheck_of_K SA.bind SB.bind
    ((rfl : thSevenRot.seedA = CertificateChecks.KernelLC.thSeedA).trans SA.eq)
    ((rfl : thSevenRot.seedB = CertificateChecks.KernelLC.thSeedB).trans SB.eq)
    (CFSG.KC.OpsF2K.sqK_of_Q CertificateChecks.KernelLC.ThSq.rot_Q)

end Certificates
