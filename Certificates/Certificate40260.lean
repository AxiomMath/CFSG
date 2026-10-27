module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermData
import Certificates.Kernel.FongPerm.C40260
import CFSG.Certificates.Kernel.FongPermSound

public section

namespace CertificateChecks.KernelFongPerm

open CFSG.KC.FongPerm CFSG.KC.LQT.P CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

private theorem code_m12a : code PermGens.m12a = code12a := by decide +kernel
private theorem code_m12b : code PermGens.m12b = code12b := by decide +kernel
private theorem code_m23a : code PermGens.m23a = code23a := by decide +kernel
private theorem code_m23b : code PermGens.m23b = code23b := by decide +kernel
private theorem code_m24a : code PermGens.m24a = code24a := by decide +kernel
private theorem code_m24b : code PermGens.m24b = code24b := by decide +kernel

end CertificateChecks.KernelFongPerm

namespace Certificates

open CFSG.KC.FongPerm CertificateChecks.KernelFongPerm

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal in
theorem certificate40260 : PGen.check PermGens.m24a PermGens.m24b m24_7_claims = true ∧
    PSec.check canonPerm PermGens.m12a PermGens.m12b m12_5_claims = true ∧
    PSec.check canonPerm PermGens.m23a PermGens.m23b m23_7_claims = true ∧
    PSec.check canonPerm PermGens.m24a PermGens.m24b m24_5_claims = true :=
  ⟨by rw [← checkK_eq (by norm_num), code_m24a, code_m24b]; exact ok40260_gen24,
    by rw [← secK_eq (by norm_num), code_m12a, code_m12b]; exact ok40260_sec12,
    by rw [← secK_eq (by norm_num), code_m23a, code_m23b]; exact ok40260_sec23,
    by rw [← secK_eq (by norm_num), code_m24a, code_m24b]; exact ok40260_sec24⟩

end Certificates
