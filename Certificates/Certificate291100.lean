module

public import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
import CFSG.Certificates.Kernel.OpsLayKSound
import Certificates.Kernel.LocalComp.F3.Fi22
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3

open CFSG.SectionRank.Native in
theorem certificate291100 : ((ops3 77).squareCheck fi22MultFive = true) :=
  CFSG.KC.OpsLayK.sqK_sound Fi22.lay_ok rfl rfl Fi22.decA Fi22.decB
    ((rfl : (fi22MultFive ()).seedA = CFSG.Blueprint.NativeSporadic.Fi22Seed1).trans Fi22.LA_eq)
    ((rfl : (fi22MultFive ()).seedB = CFSG.Blueprint.NativeSporadic.Fi22Seed2).trans Fi22.LB_eq)
    Fi22.five_K

end Certificates
