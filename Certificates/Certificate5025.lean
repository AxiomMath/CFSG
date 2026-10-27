module

public import Certificates.Data.CFSGNative.Filter.Co2Data
import CFSG.Certificates.Kernel.OpsF2KSound
import Certificates.Kernel.LocalComp.Co2Ops
public import CFSG.GH74.Filter.Witness

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.Co2Ops

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Filter in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate5025 : (ops2 22).secCheck co2Sec = true :=
  CFSG.KC.OpsF2K.secCheck_of_K SA.bind SB.bind
    ((rfl : co2Sec.seedA = CFSG.Sporadic.Co2.Native.seedA).trans SA.eq)
    ((rfl : co2Sec.seedB = CFSG.Sporadic.Co2.Native.seedB).trans SB.eq) sec_K

end Certificates
