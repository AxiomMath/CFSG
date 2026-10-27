module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi22W4Data
import CFSG.Certificates.Kernel.OpsW4NSound
import Certificates.Kernel.Census.W4Fi22
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Certificate9109
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Census CFSG.KD.LC.F3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Census CFSG.Blueprint
  CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate8156 : W4Data.check (ops3 77) fi22W4 = true :=
  CFSG.KC.OpsW4N.w4Check_of_L Fi22.lay_ok rfl rfl Fi22.decA Fi22.decB
    ((rfl : fi22W4.base.seedA = CFSG.Blueprint.NativeSporadic.Fi22Seed1).trans Fi22.LA_eq)
    ((rfl : fi22W4.base.seedB = CFSG.Blueprint.NativeSporadic.Fi22Seed2).trans Fi22.LB_eq)
    KernelCensus.W4Fi22.fi22_K

end Certificates
