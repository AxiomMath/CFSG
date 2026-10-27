
module

public import Certificates.Certificate8024Base

public import Certificates.Data.CFSGNative.SectionRank.J4Local
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsF2KCubQSound
import Certificates.Kernel.LocalComp.J4CubQ
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.J4R

open CFSG CFSG.SectionRank CFSG.SectionRank.Native in
open scoped commutatorElement in
theorem certificate8024 : ((ops2 112).cubicCheck j4Sylow3Data = true)
    ∧ ((ops2 112).cubicCheck j4Sylow11Data = true) :=
  ⟨CFSG.KC.OpsF2K.cubicCheck_of_Q JA.bind JB.bind
    ((rfl : j4Sylow3Data.seedA = CFSG.Blueprint.NativeSporadic.J4Seed1).trans JA.eq)
    ((rfl : j4Sylow3Data.seedB = CFSG.Blueprint.NativeSporadic.J4Seed2).trans JB.eq)
    j4_3Q,
  CFSG.KC.OpsF2K.cubicCheck_of_Q JA.bind JB.bind
    ((rfl : j4Sylow11Data.seedA = CFSG.Blueprint.NativeSporadic.J4Seed1).trans JA.eq)
    ((rfl : j4Sylow11Data.seedB = CFSG.Blueprint.NativeSporadic.J4Seed2).trans JB.eq)
    j4_11Q⟩

end Certificates
