module

public import Certificates.Data.RankThree46Odd.Suz
public import Certificates.Data.CFSGNative.SectionRank.F3
import CFSG.Certificates.Kernel.OpsW4NSound
import Certificates.Kernel.Census.W4Suz
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Census CFSG.KD.LC.F3

open CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native in
theorem certificate8089 : W4Data.check (ops3 64) suzW3 = true :=
  CFSG.KC.OpsW4N.w4Check_of_L Suz.lay_ok rfl rfl Suz.decA Suz.decB
    ((rfl : suzW3.base.seedA = CFSG.Blueprint.NativeSporadic.SuzSeed1).trans Suz.LA_eq)
    ((rfl : suzW3.base.seedB = CFSG.Blueprint.NativeSporadic.SuzSeed2).trans Suz.LB_eq)
    KernelCensus.W4Suz.suz_K

end Certificates
