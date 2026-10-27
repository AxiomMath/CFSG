module

public import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.Fi23
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3

open CFSG.SectionRank.Native in
theorem certificate291101 : ((ops3 253).squareCheck fi23MultFive = true) :=
  CFSG.KC.OpsLayK.sqK_sound Fi23.lay_ok rfl rfl Fi23.decA Fi23.decB
    ((rfl : (fi23MultFive ()).seedA = CFSG.Blueprint.NativeSporadic.Fi23Seed1).trans Fi23.LA_eq)
    ((rfl : (fi23MultFive ()).seedB = CFSG.Blueprint.NativeSporadic.Fi23Seed2).trans Fi23.LB_eq)
    Fi23.five_K

end Certificates
