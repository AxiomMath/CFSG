module

public import Certificates.Data.CFSGNative.Filter.ThData
import CFSG.Certificates.Kernel.OpsF2KSound
import CFSG.Certificates.Kernel.OpsF2KQSound
import Certificates.Kernel.LocalComp.ThSecQ
public import CFSG.GH74.Filter.Witness

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.Th8

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Filter in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate5037 : (ops2 248).secCheck thSec = true :=
  CFSG.KC.OpsF2K.secCheck_of_K SA.bind SB.bind
    ((rfl : thSec.seedA = CertificateChecks.KernelLC.thSeedA).trans SA.eq)
    ((rfl : thSec.seedB = CertificateChecks.KernelLC.thSeedB).trans SB.eq)
    (CFSG.KC.OpsF2K.secK_of_Q CertificateChecks.KernelLC.ThSec.sec_Q)

end Certificates
