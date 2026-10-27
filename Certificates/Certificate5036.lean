module

public import Certificates.Data.CFSGNative.Filter.SuzData
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.Suz
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
theorem certificate5036 : (ops3 64).secCheck suzSec = true :=
  CFSG.KC.OpsLayK.secK_sound Suz.lay_ok rfl rfl Suz.decA Suz.decB
    ((rfl : suzSec.seedA = CFSG.Blueprint.NativeSporadic.SuzSeed1).trans Suz.LA_eq)
    ((rfl : suzSec.seedB = CFSG.Blueprint.NativeSporadic.SuzSeed2).trans Suz.LB_eq) Suz.sec_K

end Certificates
