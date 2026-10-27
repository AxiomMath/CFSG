module

public import Certificates.Data.SporadicTwoCover
import CFSG.Certificates.Kernel.OpsLaySignedSound
import Certificates.Kernel.OpsLaySigned.ON

public section

open CertificateChecks.KernelFusLay CertificateChecks.KernelOpsLaySigned

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native in
open CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCover.Native in
theorem certificate8094 : e8Check (ops3 154) onE8Data = true :=
  CFSG.KC.OpsLaySigned.e8K3_sound ON.lay_ok rfl rfl ON.decA ON.decB ON.e8_8094_seedA
    ON.e8_8094_seedB ON.e8_8094_K

end Certificates
