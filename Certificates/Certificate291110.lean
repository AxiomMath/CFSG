module

public import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
import CFSG.Certificates.Kernel.LocalCompSqReplaySound
import Certificates.Kernel.LocalComp.F3.Fi24Five
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3

open CFSG.SectionRank.Native in
theorem certificate291110 : ((ops3 781).squareCheck fi24MultFive = true) :=
  CFSG.KC.LocalComp.Replay.squareCheck_of_K Fi24Five.lay_ok rfl rfl
    ((rfl : (fi24MultFive ()).seedA = CFSG.Blueprint.NativeSporadic.Fi24primeSeed1).trans
      Fi24Five.LA_eq)
    ((rfl : (fi24MultFive ()).seedB = CFSG.Blueprint.NativeSporadic.Fi24primeSeed2).trans
      Fi24Five.LB_eq)
    Fi24Five.decA Fi24Five.decB Fi24Five.one Fi24Five.steps Fi24Five.replay Fi24Five.sq

end Certificates
