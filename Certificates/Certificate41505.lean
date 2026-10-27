module

public import Certificates.Data.WCSporRot
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.Suz
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3

open CFSG.SectionRank.Native in
theorem certificate41505 : (ops3 64).squareCheck suzFiveRot = true :=
  CFSG.KC.OpsLayK.sqK_sound Suz.lay_ok rfl rfl Suz.decA Suz.decB
    ((rfl : suzFiveRot.seedA = CFSG.Blueprint.NativeSporadic.SuzSeed1).trans Suz.LA_eq)
    ((rfl : suzFiveRot.seedB = CFSG.Blueprint.NativeSporadic.SuzSeed2).trans Suz.LB_eq)
    Suz.rot_K

end Certificates
