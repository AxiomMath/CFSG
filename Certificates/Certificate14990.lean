module

public import Certificates.Data.CFSGNative.MultRes.Witnesses
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.McL
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3

open CFSG.SectionRank.Native in
theorem certificate14990 : ((ops3 21).cubicCheck mclMultData = true) :=
  CFSG.KC.OpsLayK.cubK_sound McL.lay_ok rfl rfl McL.decA McL.decB
    ((rfl : mclMultData.seedA = CFSG.Blueprint.NativeSporadic.McLSeed1).trans McL.LA_eq)
    ((rfl : mclMultData.seedB = CFSG.Blueprint.NativeSporadic.McLSeed2).trans McL.LB_eq)
    McL.mult_K

end Certificates
