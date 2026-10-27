module

public import Certificates.Data.RankThree46Odd.ON
public import Certificates.Data.CFSGNative.SectionRank.F3
import CFSG.Certificates.Kernel.OpsV4Sound
import Certificates.Kernel.Census.V4ON
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Census
open CertificateChecks.KernelTc.ON (lay_ok decA decB LA_eq LB_eq)

open CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native in
theorem certificate8092 : V4Data.check (ops3 154) onV4 = true :=
  CFSG.KC.OpsV4.v4Check_of_L lay_ok rfl rfl decA decB
    ((rfl : onV4.base.seedA = CFSG.Blueprint.NativeSporadic.ONSeed1).trans LA_eq)
    ((rfl : onV4.base.seedB = CFSG.Blueprint.NativeSporadic.ONSeed2).trans LB_eq)
    CFSG.KD.V4ON.on_K

end Certificates

end
