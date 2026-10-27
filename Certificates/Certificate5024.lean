module

public import Certificates.Data.CFSGNative.Filter.Co1Data
import CFSG.Certificates.Kernel.OpsF2KSound
import Certificates.Kernel.LocalComp.Co1Ops
public import CFSG.GH74.Filter.Witness

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.Co1Ops

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Filter in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate5024 : (ops2 24).secCheck co1Sec = true :=
  CFSG.KC.OpsF2K.secCheck_of_K SA.bind SB.bind
    ((rfl : co1Sec.seedA = CFSG.Sporadic.Co1.Native.seedA).trans SA.eq)
    ((rfl : co1Sec.seedB = CFSG.Sporadic.Co1.Native.seedB).trans SB.eq) sec_K

end Certificates
