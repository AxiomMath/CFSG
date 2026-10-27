module

public import Certificates.Data.CFSGNative.CTP.Fi24Sylow7
import CFSG.Certificates.Kernel.LocalCompCubPartsSound
import Certificates.Kernel.LocalComp.F3.Fi24Sylow7
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3

open CFSG.SectionRank.Native in
theorem certificate9486 : (ops3 781).cubicCheck fi24Sylow7Data = true :=
  CFSG.KC.LocalComp.CubParts.cubicCheck_of_parts Fi24Sylow7.lay_ok rfl rfl
    ((rfl : fi24Sylow7Data.seedA = CFSG.Blueprint.NativeSporadic.Fi24primeSeed1).trans
      Fi24Sylow7.LA_eq)
    ((rfl : fi24Sylow7Data.seedB = CFSG.Blueprint.NativeSporadic.Fi24primeSeed2).trans
      Fi24Sylow7.LB_eq)
    Fi24Sylow7.decA Fi24Sylow7.decB Fi24Sylow7.one Fi24Sylow7.steps Fi24Sylow7.replay
    Fi24Sylow7.parts Fi24Sylow7.vt0 Fi24Sylow7.vtab (by decide) Fi24Sylow7.sort

end Certificates
