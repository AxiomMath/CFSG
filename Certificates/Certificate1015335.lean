module

public import Certificates.Data.J4SylowThreeIrr
import CFSG.Certificates.Kernel.OpsF2KCubQSound
import Certificates.Kernel.LocalComp.J4CubQ
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.J4R

open CFSG.SectionRank.Native in
theorem certificate1015335 : (ops2 112).cubicCheck j4Sylow3IrrData = true :=
  CFSG.KC.OpsF2K.cubicCheck_of_Q JA.bind JB.bind
    ((rfl : j4Sylow3IrrData.seedA = CFSG.Blueprint.NativeSporadic.J4Seed1).trans JA.eq)
    ((rfl : j4Sylow3IrrData.seedB = CFSG.Blueprint.NativeSporadic.J4Seed2).trans JB.eq)
    j4_3irrQ

end Certificates
