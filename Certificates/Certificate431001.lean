module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi22LiftData
import CFSG.Certificates.Kernel.OpsV4Sound
import Certificates.Kernel.Census.LiftFi22
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Census CFSG.KD.LC.F3

open CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native in
theorem certificate431001 : LiftData.check (ops3 77) fi22Lift = true :=
  CFSG.KC.OpsV4.liftCheck_of_L Fi22.lay_ok rfl rfl Fi22.decA Fi22.decB
    ((rfl : fi22Lift.base.seedA = CFSG.Blueprint.NativeSporadic.Fi22Seed1).trans Fi22.LA_eq)
    ((rfl : fi22Lift.base.seedB = CFSG.Blueprint.NativeSporadic.Fi22Seed2).trans Fi22.LB_eq)
    KernelCensus.LiftFi22.fi22_K

end Certificates
