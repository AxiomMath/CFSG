module

public import Certificates.Data.CFSGNative.Filter.Co3Data
import CFSG.Certificates.Kernel.OpsF2KSound
import Certificates.Kernel.LocalComp.Co3Ops
public import CFSG.GH74.Filter.Witness

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.Co3Ops

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Filter in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate5026 : (ops2 22).secCheck co3Sec = true :=
  CFSG.KC.OpsF2K.secCheck_of_K SA.bind SB.bind
    ((rfl : co3Sec.seedA = CFSG.Sporadic.Co3.Native.seedA).trans SA.eq)
    ((rfl : co3Sec.seedB = CFSG.Sporadic.Co3.Native.seedB).trans SB.eq) sec_K

end Certificates
