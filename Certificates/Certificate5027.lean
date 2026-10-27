module

public import Certificates.Data.CFSGNative.Filter.Fi22Data
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.Fi22
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
theorem certificate5027 : (ops3 77).secCheck fi22Sec = true :=
  CFSG.KC.OpsLayK.secK_sound Fi22.lay_ok rfl rfl Fi22.decA Fi22.decB
    ((rfl : fi22Sec.seedA = CFSG.Blueprint.NativeSporadic.Fi22Seed1).trans Fi22.LA_eq)
    ((rfl : fi22Sec.seedB = CFSG.Blueprint.NativeSporadic.Fi22Seed2).trans Fi22.LB_eq) Fi22.sec_K

end Certificates
