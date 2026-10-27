module

public import Certificates.Data.CFSGNative.MultRes.Witnesses
import CFSG.Certificates.Kernel.OpsF2KCubQSound
import CFSG.Certificates.Kernel.OpsF2KSqSound
import CFSG.Certificates.Kernel.OpsF2KSqQSound
import Certificates.Kernel.LocalComp.ThCubQ
import Certificates.Kernel.LocalComp.ThSqQ

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.Th8

open CFSG.SectionRank.Native in
theorem certificate14992 : ((ops2 248).cubicCheck thMultData5 = true)
    ∧ ((ops2 248).squareCheck thMultData7 = true) :=
  ⟨CFSG.KC.OpsF2K.cubicCheck_of_Q SA.bind SB.bind
    ((rfl : thMultData5.seedA = CertificateChecks.KernelLC.thSeedA).trans SA.eq)
    ((rfl : thMultData5.seedB = CertificateChecks.KernelLC.thSeedB).trans SB.eq)
    CertificateChecks.KernelLC.ThCub.cub_Q,
  CFSG.KC.OpsF2K.squareCheck_of_K SA.bind SB.bind
    ((rfl : thMultData7.seedA = CertificateChecks.KernelLC.thSeedA).trans SA.eq)
    ((rfl : thMultData7.seedB = CertificateChecks.KernelLC.thSeedB).trans SB.eq)
    (CFSG.KC.OpsF2K.sqK_of_Q CertificateChecks.KernelLC.ThSq.sq7_Q)⟩

end Certificates
