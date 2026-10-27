module

public import Certificates.Data.CFSGNative.MultRes.Witnesses
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.ON
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3

open CFSG.SectionRank.Native in
theorem certificate14995 : ((ops3 154).cubicCheck onMultData = true) :=
  CFSG.KC.OpsLayK.cubK_sound ON.lay_ok rfl rfl ON.decA ON.decB
    ((rfl : onMultData.seedA = CFSG.Blueprint.NativeSporadic.ONSeed1).trans ON.LA_eq)
    ((rfl : onMultData.seedB = CFSG.Blueprint.NativeSporadic.ONSeed2).trans ON.LB_eq)
    ON.mult_K

end Certificates
