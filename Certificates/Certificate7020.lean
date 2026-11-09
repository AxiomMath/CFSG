module

public import CFSG.Quasithin.H13.NQCatJ4Native
import CFSG.Certificates.Kernel.J4FixSound
import Certificates.Kernel.LocalComp.J4FixC
import Certificates.Kernel.LocalComp.J4FixReps
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CertificateChecks.KernelLC.J4R CertificateChecks.KernelLC.J4Fix

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.NQCat CFSG.Quasithin.H13.NQCat.Native in
open CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native in
theorem certificate7020 :
    ((ops2 112).eq ((ops2 112).pow j4H 40) (ops2 112).one = true)
    ∧ ((ops2 112).conjOK j4H j4X (j4Word 0 7 1) = true)
    ∧ ((ops2 112).conjOK j4H j4Y (j4Word 6 9 6) = true)
    ∧ ((ops2 112).conjOK j4H j4Z (CFSG.Sporadic.SmallF2.Native.powRows 112 j4Z 2) = true)
    ∧ (j4FixRepsOK = true)
    ∧ (fixDimOK 112 j4Z 2 = true) :=
  CFSG.KC.J4Fix.check_of_K JA.bind JB.bind
    ((rfl : j4Sylow11Data.seedA = CFSG.Blueprint.NativeSporadic.J4Seed1).trans JA.eq)
    ((rfl : j4Sylow11Data.seedB = CFSG.Blueprint.NativeSporadic.J4Seed2).trans JB.eq)
    h40_K conjX_K conjY_K conjZ_K reps_K central_K

end Certificates
