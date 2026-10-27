module

public import Certificates.Data.KFCub2McL
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.McL
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3

theorem certificate40023 : (CFSG.SectionRank.Native.ops3 21).cub2Check CFSG.SectionRank.Native.mclFiveData = true :=
  CFSG.KC.OpsLayK.cub2K_sound McL.lay_ok rfl rfl McL.decA McL.decB
    ((rfl : mclFiveData.seedA = CFSG.Blueprint.NativeSporadic.McLSeed1).trans McL.LA_eq)
    ((rfl : mclFiveData.seedB = CFSG.Blueprint.NativeSporadic.McLSeed2).trans McL.LB_eq)
    McL.five_K

end Certificates
