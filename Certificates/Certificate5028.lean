module

public import Certificates.Data.CFSGNative.Filter.Fi23Data
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.Fi23
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
theorem certificate5028 : (ops3 253).secCheck fi23Sec = true :=
  CFSG.KC.OpsLayK.secK_sound Fi23.lay_ok rfl rfl Fi23.decA Fi23.decB
    ((rfl : fi23Sec.seedA = CFSG.Blueprint.NativeSporadic.Fi23Seed1).trans Fi23.LA_eq)
    ((rfl : fi23Sec.seedB = CFSG.Blueprint.NativeSporadic.Fi23Seed2).trans Fi23.LB_eq) Fi23.sec_K

end Certificates
