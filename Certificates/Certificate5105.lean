module

public import CFSG.GH74.Generic.GKFMcLInputs
import CFSG.Certificates.Kernel.OpsLayGKFSound
import Certificates.Kernel.OpsLaySigned.McLFus

public section

open CertificateChecks.KernelFusLay CertificateChecks.KernelOpsLaySigned

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Generic in
open CFSG CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.GH74.Generic.Fusion Subgroup in
theorem certificate5105 : CFSG.GH74.Generic.Fusion.fusCheck (ops3 21) mclFus = true :=
  CFSG.KC.OpsLayGKF.gkfFusK_sound McL.lay_ok rfl rfl McL.decA McL.decB McL.fus5105_seedA
    McL.fus5105_seedB McL.fus5105_K

end Certificates
