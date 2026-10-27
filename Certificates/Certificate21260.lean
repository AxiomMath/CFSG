module

public import Certificates.Kernel.SmithEK.ChkTW

public section

namespace Certificates

open CertificateChecks.KernelSmithEK in
theorem certificate21260 :
    CFSG.SmithE.chkTvInv = true ∧ CFSG.SmithE.chkTvConj = true ∧
      CFSG.SmithE.chkPtWords = true ∧ CFSG.SmithE.chkPairWords = true ∧
      CFSG.SmithE.chkPlaneWords = true ∧ CFSG.SmithE.chkTW = true ∧
      CFSG.SmithE.chkPlanes = true ∧ CFSG.SmithE.chkGram = true ∧
      CFSG.SmithE.chkFormInv = true :=
  ⟨chkTvInv_eq, chkTvConj_eq, chkPtWords_eq, chkPairWords_eq, chkPlaneWords_eq, chkTW_eq,
    chkPlanes_eq, chkGram_eq, chkFormInv_eq⟩

end Certificates
