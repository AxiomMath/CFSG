module

public import Certificates.Data.SmithB45ExcHe
import Certificates.Kernel.MatCert.HeInv
import CFSG.Certificates.Kernel.OpsCubNSound
import CFSG.Certificates.Kernel.OpsFpKSound
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace Certificates

open CFSG.KC.OpsCubN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.KS.SporSch.LyM CFSG.SectionRank.Native
open CFSG.Quasithin.B45Exc CFSG.Blueprint CertificateChecks.KernelMC

open CFSG.SectionRank.Native CFSG.Quasithin.B45Exc in
theorem certificate260382 : (opsP 7 50).cubicCheck heInvData = true := by
  have h := heInv_K
  rw [forceB_eq, forceB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hB⟩, h⟩ := h
  refine cubicCheck_of_N (homP heConsts (by norm_num)) ?_ ?_ hA hB h
  · change (opsP 7 50).decode NativeSporadic.HeSeed1 = _
    rw [HeS1.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)
  · change (opsP 7 50).decode NativeSporadic.HeSeed2 = _
    rw [HeS2.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)

end Certificates
