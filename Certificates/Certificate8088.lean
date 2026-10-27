module

public import Certificates.Data.RankThree46F2.Th
public import Certificates.Data.CFSGNative.SectionRank.F2
import CFSG.Certificates.Kernel.OpsF2KSound
import CFSG.Certificates.Kernel.OpsF2KQSound
import Certificates.Kernel.Census.W4ThQ

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Census CertificateChecks.Th8

open CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native in
theorem certificate8088 : W4Data.check (ops2 248) thW3 = true :=
  CFSG.KC.OpsF2K.w4Check_of_K SA.bind SB.bind
    ((rfl : thW3.base.seedA = CertificateChecks.KernelLC.thSeedA).trans SA.eq)
    ((rfl : thW3.base.seedB = CertificateChecks.KernelLC.thSeedB).trans SB.eq)
    (CFSG.KC.OpsF2K.w4K_of_Q KernelCensus.W4Th.th_Q)

end Certificates
