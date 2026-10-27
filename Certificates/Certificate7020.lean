module

public import CFSG.Quasithin.H13.NQCatJ4Native
import CFSG.Certificates.Kernel.J4FixSound
import Certificates.Kernel.LocalComp.J4FixC
import Certificates.Kernel.LocalComp.J4FixR0
import Certificates.Kernel.LocalComp.J4FixR1
import Certificates.Kernel.LocalComp.J4FixR2
import Certificates.Kernel.LocalComp.J4FixR3
import Certificates.Kernel.LocalComp.J4FixR4
import Certificates.Kernel.LocalComp.J4FixR5
import Certificates.Kernel.LocalComp.J4FixR6
import Certificates.Kernel.LocalComp.J4FixR7
import Certificates.Kernel.LocalComp.J4FixR8
import Certificates.Kernel.LocalComp.J4FixR9
import Certificates.Kernel.LocalComp.J4FixR10
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
    ∧ (j4FixNoncentralOK = true)
    ∧ (j4FixCentralOK = true)
    ∧ (j4PowXYOK = true) :=
  CFSG.KC.J4Fix.check_of_K JA.bind JB.bind
    ((rfl : j4Sylow11Data.seedA = CFSG.Blueprint.NativeSporadic.J4Seed1).trans JA.eq)
    ((rfl : j4Sylow11Data.seedB = CFSG.Blueprint.NativeSporadic.J4Seed2).trans JB.eq)
    h40_K conjX_K conjY_K conjZ_K
    (fun i hi => by
      match i, hi with
      | 0, _ => exact row0_K
      | 1, _ => exact row1_K
      | 2, _ => exact row2_K
      | 3, _ => exact row3_K
      | 4, _ => exact row4_K
      | 5, _ => exact row5_K
      | 6, _ => exact row6_K
      | 7, _ => exact row7_K
      | 8, _ => exact row8_K
      | 9, _ => exact row9_K
      | 10, _ => exact row10_K)
    central_K powXY_K

end Certificates
