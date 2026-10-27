module

public import Certificates.Data.SporadicTwoCover
import CFSG.Certificates.Kernel.OpsF2KE16Sound
import Certificates.Kernel.J3E16.Chk

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCover.Native
open CertificateChecks.KernelLC.J3Ops

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native in
open CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCover.Native in
theorem certificate8095 : e16Check (ops2 80) j3E16Data = true :=
  CFSG.KC.OpsF2K.e16Check_of_K SA.bind SB.bind
    ((rfl : j3E16Data.seedA = CFSG.Sporadic.J3.Native.seedA).trans SA.eq)
    ((rfl : j3E16Data.seedB = CFSG.Sporadic.J3.Native.seedB).trans SB.eq)
    CertificateChecks.KernelJ3E16.e16_K

end Certificates
