module

public import Certificates.Data.J3Comm
import CFSG.Certificates.Kernel.OpsF2KEnumSound
import Certificates.Kernel.LocalComp.J3Enum

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.J3Ops

open CFSG.SectionRank.Native in
theorem certificate39140 : (ops2 80).commTripleCheck j3CommTripleData = true :=
  CFSG.KC.OpsF2K.commTripleCheck_of_K SA.bind SB.bind
    ((rfl : j3CommTripleData.base.seedA = CFSG.Sporadic.J3.Native.seedA).trans SA.eq)
    ((rfl : j3CommTripleData.base.seedB = CFSG.Sporadic.J3.Native.seedB).trans SB.eq)
    CertificateChecks.KernelLC.J3Enum.comm_K

end Certificates
