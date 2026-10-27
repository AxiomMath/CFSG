module

public import CFSG.GH74.Generic.GKFLyInputs
import CFSG.Certificates.Kernel.OpsLayGKFTSound
import Certificates.Kernel.FusLay.LyGKF

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Generic in
open CFSG CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.GH74.Generic.Fusion Subgroup in
theorem certificate5104 : fusCheck (opsP 5 111) lyFus = true :=
  CFSG.KC.OpsLayGKF.gkfFusKP_sound Ly.lay_ok rfl rfl Ly.decA Ly.decB Ly.fus5104_seedA
    Ly.fus5104_seedB ((CFSG.KC.OpsLayGKF.gkfFusKT_eq _ _ _ _).symm.trans Ly.fus5104_K)

end Certificates
