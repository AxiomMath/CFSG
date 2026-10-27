module

public import Certificates.Data.CFSGNative.Filter.RuData
import CFSG.Certificates.Kernel.OpsF2KSound
import Certificates.Kernel.LocalComp.RuOps
public import CFSG.GH74.Filter.Witness

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.RuOps

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Filter in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate5035 : (ops2 28).secCheck ruSec = true :=
  CFSG.KC.OpsF2K.secCheck_of_K SA.bind SB.bind
    ((rfl : ruSec.seedA = CFSG.Sporadic.Ru.Native.seedA).trans SA.eq)
    ((rfl : ruSec.seedB = CFSG.Sporadic.Ru.Native.seedB).trans SB.eq) sec_K

end Certificates
