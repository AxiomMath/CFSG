module

public import Certificates.Data.CFSGNative.Filter.J4Data
import CFSG.Certificates.Kernel.OpsF2KSound
import CFSG.Certificates.Kernel.OpsF2KQSound
import Certificates.Kernel.LocalComp.J4SecQ
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.GH74.Filter.Witness

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.J4R

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Filter in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate5033 : (ops2 112).secCheck j4Sec = true :=
  CFSG.KC.OpsF2K.secCheck_of_K JA.bind JB.bind
    ((rfl : j4Sec.seedA = CFSG.Blueprint.NativeSporadic.J4Seed1).trans JA.eq)
    ((rfl : j4Sec.seedB = CFSG.Blueprint.NativeSporadic.J4Seed2).trans JB.eq)
    (CFSG.KC.OpsF2K.secK_of_Q CertificateChecks.KernelLC.J4Sec.sec_Q)

end Certificates
