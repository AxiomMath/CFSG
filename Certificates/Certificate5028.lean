module

public import Certificates.Data.CFSGNative.Filter.Fi23Data
import CFSG.Certificates.Kernel.LocalCompCubPartsSound
import Certificates.Kernel.LocalComp.F3.Fi23Sec
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
  CFSG.KC.LocalComp.CubParts.secCheck_of_parts Fi23Sec.lay_ok rfl rfl
    ((rfl : fi23Sec.seedA = CFSG.Blueprint.NativeSporadic.Fi23Seed1).trans Fi23Sec.LA_eq)
    ((rfl : fi23Sec.seedB = CFSG.Blueprint.NativeSporadic.Fi23Seed2).trans Fi23Sec.LB_eq)
    Fi23Sec.decA Fi23Sec.decB Fi23Sec.one Fi23Sec.steps rfl Fi23Sec.replay Fi23Sec.parts
    Fi23Sec.vt0 Fi23Sec.vtab (by decide) Fi23Sec.kmod

end Certificates
