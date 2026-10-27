module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1W4Data
import CFSG.Certificates.Kernel.OpsF2KSound
import CFSG.Certificates.Kernel.OpsF2KQSound
import Certificates.Kernel.Census.W4F2Q
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Certificate3024Base
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Census CertificateChecks.KernelAM

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Census CFSG.Blueprint
  CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate8153 : W4Data.check (ops2 24) co1W4 = true :=
  CFSG.KC.OpsF2K.w4Check_of_K C1A.bind C1B.bind
    ((rfl : co1W4.base.seedA = CFSG.Blueprint.NativeSporadic.Co1Seed1).trans C1A.eq)
    ((rfl : co1W4.base.seedB = CFSG.Blueprint.NativeSporadic.Co1Seed2).trans C1B.eq)
    (CFSG.KC.OpsF2K.w4K_of_Q KernelCensus.W4F2.co1_Q)

end Certificates
