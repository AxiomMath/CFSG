module

public import CFSG.GH74.E2.CompCertsJ3Inputs
import CFSG.Certificates.Kernel.OpsF2KSound
import CFSG.Certificates.Kernel.OpsF2KQSound
import Certificates.Kernel.LocalComp.J3OpsQ

public section

namespace Certificates

open CFSG.GH74.E2 CertificateChecks.KernelLC.J3Ops

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.GH74.Generic in
theorem certificate5007 : (ops2 80).secCheck j3Sec = true :=
  CFSG.KC.OpsF2K.secCheck_of_K SA.bind SB.bind
    ((rfl : j3Sec.seedA = CFSG.Sporadic.J3.Native.seedA).trans SA.eq)
    ((rfl : j3Sec.seedB = CFSG.Sporadic.J3.Native.seedB).trans SB.eq)
    (CFSG.KC.OpsF2K.secK_of_Q sec_Q)

end Certificates
