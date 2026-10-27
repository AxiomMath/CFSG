module

public import Certificates.Data.RankThree46F2.Co3
public import Certificates.Data.CFSGNative.SectionRank.F2
import CFSG.Certificates.Kernel.OpsF2KSound
import CFSG.Certificates.Kernel.OpsF2KQSound
import Certificates.Kernel.Census.W4F2Q
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Census CertificateChecks.KernelAM

open CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native in
theorem certificate8086 : W4Data.check (ops2 22) co3W3 = true :=
  CFSG.KC.OpsF2K.w4Check_of_K C3A.bind C3B.bind
    ((rfl : co3W3.base.seedA = CFSG.Blueprint.NativeSporadic.Co3Seed1).trans C3A.eq)
    ((rfl : co3W3.base.seedB = CFSG.Blueprint.NativeSporadic.Co3Seed2).trans C3B.eq)
    (CFSG.KC.OpsF2K.w4K_of_Q KernelCensus.W4F2.co3_Q)

end Certificates
