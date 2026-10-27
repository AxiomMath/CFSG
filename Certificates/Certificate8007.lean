module

public import Certificates.Data.CoverCenterThreeON
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.ON
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3

open CFSG.SectionRank.Native in
theorem certificate8007 : (ops3 154).normCheck onNormData = true :=
  CFSG.KC.OpsLayK.normCK_sound ON.lay_ok rfl rfl ON.decA ON.decB
    ((rfl : onNormData.base.seedA = CFSG.Blueprint.NativeSporadic.ONSeed1).trans ON.LA_eq)
    ((rfl : onNormData.base.seedB = CFSG.Blueprint.NativeSporadic.ONSeed2).trans ON.LB_eq)
    ON.norm_K

end Certificates
