module

public import Certificates.Data.CFSGNative.Filter.ONData
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.ON
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.GH74.Filter.Witness

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Filter in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate5034 : (ops3 154).secCheck onanSec = true :=
  CFSG.KC.OpsLayK.secK_sound ON.lay_ok rfl rfl ON.decA ON.decB
    ((rfl : onanSec.seedA = CFSG.Blueprint.NativeSporadic.ONSeed1).trans ON.LA_eq)
    ((rfl : onanSec.seedB = CFSG.Blueprint.NativeSporadic.ONSeed2).trans ON.LB_eq) ON.sec_K

end Certificates
