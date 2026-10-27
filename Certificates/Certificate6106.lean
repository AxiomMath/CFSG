module

public import CFSG.Sporadic.Recognition.McLASThreeLocalInputs
public meta import CFSG.Sporadic.Recognition.McLASThreeLocalInputs
import Certificates.Kernel.Sporadic.OddCore.McLTH

public section

open CFSG.Sporadic.Recognition.McLAS

namespace CertificateChecks.Batch6106

open CFSG.Sporadic.Recognition.McLAS

open CertificateChecks.KernelSpor.McLTK

private theorem threeEnumCheck_0 : threeEnumCheck = true := threeEnum_ok

private theorem gxCheck_1 : gxCheck = true := gx_ok

private theorem rInTCheck_2 : rInTCheck = true := rInT_ok

private theorem rNormalCheck_3 : rNormalCheck = true := rNormal_ok

private theorem sylowIntCheck_4 : sylowIntCheck = true := sylowInt_ok

private theorem rStructCheck_5 : rStructCheck = true := rStruct_ok

private theorem aStructCheck_6 : aStructCheck = true := aStruct_ok

private theorem aInvCheck_7 : aInvCheck = true := aInv_ok

private theorem weakCheck_8 : weakCheck = true := weak_ok

private theorem thompsonCheck_9 : thompsonCheck = true := thompson_ok

end CertificateChecks.Batch6106

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.McLAS in
theorem certificate6106 : (threeEnumCheck = true) ∧ (gxCheck = true) ∧ (rInTCheck = true) ∧
    (rNormalCheck = true) ∧ (sylowIntCheck = true) ∧ (rStructCheck = true) ∧
    (aStructCheck = true) ∧ (aInvCheck = true) ∧ (weakCheck = true) ∧ (thompsonCheck = true) := by
  exact ⟨CertificateChecks.Batch6106.threeEnumCheck_0, CertificateChecks.Batch6106.gxCheck_1, CertificateChecks.Batch6106.rInTCheck_2,
    CertificateChecks.Batch6106.rNormalCheck_3, CertificateChecks.Batch6106.sylowIntCheck_4, CertificateChecks.Batch6106.rStructCheck_5,
    CertificateChecks.Batch6106.aStructCheck_6, CertificateChecks.Batch6106.aInvCheck_7, CertificateChecks.Batch6106.weakCheck_8,
    CertificateChecks.Batch6106.thompsonCheck_9⟩

end Certificates
