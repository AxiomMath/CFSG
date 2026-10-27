module

public import Certificates.Data.RankThree46F2.Co2
public import Certificates.Data.CFSGNative.SectionRank.F2
import CFSG.Certificates.Kernel.OpsF2KSound
import Certificates.Kernel.LocalComp.Co2Ops

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Census CertificateChecks.KernelLC.Co2Ops

open CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native in
theorem certificate8087 : W4Data.check (ops2 22) co2W3 = true :=
  CFSG.KC.OpsF2K.w4Check_of_K SA.bind SB.bind
    ((rfl : co2W3.base.seedA = CFSG.Sporadic.Co2.Native.seedA).trans SA.eq)
    ((rfl : co2W3.base.seedB = CFSG.Sporadic.Co2.Native.seedB).trans SB.eq) w4_K

end Certificates
