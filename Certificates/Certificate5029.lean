module

public import Certificates.Data.CFSGNative.Filter.Fi24primeData
import CFSG.Certificates.Kernel.LocalCompCubPartsSound
import Certificates.Kernel.LocalComp.F3.Fi24Sec
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
theorem certificate5029 : (ops3 781).secCheck fi24primeSec = true :=
  CFSG.KC.LocalComp.CubParts.secCheck_of_parts Fi24Sec.lay_ok rfl rfl
    ((rfl : fi24primeSec.seedA = CFSG.Blueprint.NativeSporadic.Fi24primeSeed1).trans
      Fi24Sec.LA_eq)
    ((rfl : fi24primeSec.seedB = CFSG.Blueprint.NativeSporadic.Fi24primeSeed2).trans
      Fi24Sec.LB_eq)
    Fi24Sec.decA Fi24Sec.decB Fi24Sec.one Fi24Sec.steps rfl Fi24Sec.replay Fi24Sec.parts
    Fi24Sec.vt0 Fi24Sec.vtab (by decide) Fi24Sec.kmod

end Certificates
