module

public import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
import CFSG.Certificates.Kernel.LocalCompSqReplaySound
import Certificates.Kernel.LocalComp.F3.Fi23Five
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3

open CFSG.SectionRank.Native in
theorem certificate291101 : ((ops3 253).squareCheck fi23MultFive = true) :=
  CFSG.KC.LocalComp.Replay.squareCheck_of_K Fi23Five.lay_ok rfl rfl
    ((rfl : (fi23MultFive ()).seedA = CFSG.Blueprint.NativeSporadic.Fi23Seed1).trans
      Fi23Five.LA_eq)
    ((rfl : (fi23MultFive ()).seedB = CFSG.Blueprint.NativeSporadic.Fi23Seed2).trans
      Fi23Five.LB_eq)
    Fi23Five.decA Fi23Five.decB Fi23Five.one Fi23Five.steps Fi23Five.replay Fi23Five.sq

end Certificates
