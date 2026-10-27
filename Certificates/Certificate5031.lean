module

public import Certificates.Data.CFSGNative.Filter.HSData
import CFSG.Certificates.Kernel.OpsF2KSound
import CFSG.Certificates.Kernel.OpsF2KQSound
import Certificates.Kernel.SectionRankHS.SecQ
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.GH74.Filter.Witness

public section

open CFSG.SectionRank.Native CertificateChecks.KernelSRHS

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Filter in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate5031 : (ops2 20).secCheck hsSec = true :=
  CFSG.KC.OpsF2K.secCheck_of_K SA.bind SB.bind
    ((rfl : hsSec.seedA = CFSG.Blueprint.NativeSporadic.HSSeed1).trans SA.eq)
    ((rfl : hsSec.seedB = CFSG.Blueprint.NativeSporadic.HSSeed2).trans SB.eq)
    (CFSG.KC.OpsF2K.secK_of_Q sec_Q)

end Certificates
