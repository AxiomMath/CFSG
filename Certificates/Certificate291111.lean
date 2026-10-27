module

public import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
import CFSG.Certificates.Kernel.LocalCompCubPartsSound
import Certificates.Kernel.LocalComp.F3.Fi24Seven
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3

open CFSG.SectionRank.Native in
theorem certificate291111 : ((ops3 781).cubicCheck fi24MultSeven = true) :=
  CFSG.KC.LocalComp.CubParts.cubicCheck_of_parts Fi24Seven.lay_ok rfl rfl
    ((rfl : (fi24MultSeven ()).seedA = CFSG.Blueprint.NativeSporadic.Fi24primeSeed1).trans
      Fi24Seven.LA_eq)
    ((rfl : (fi24MultSeven ()).seedB = CFSG.Blueprint.NativeSporadic.Fi24primeSeed2).trans
      Fi24Seven.LB_eq)
    Fi24Seven.decA Fi24Seven.decB Fi24Seven.one Fi24Seven.steps Fi24Seven.replay Fi24Seven.parts
    Fi24Seven.vt0 Fi24Seven.vtab (by decide) Fi24Seven.sort

end Certificates
