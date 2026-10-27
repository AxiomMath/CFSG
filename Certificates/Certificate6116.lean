module

public import CFSG.Sporadic.Recognition.LyonsFinalFamiliesBase
public import CFSG.Sporadic.Recognition.LyonsFinalModularInputs
public import CFSG.Sporadic.Recognition.LyonsFinalDist2Inputs
public import CFSG.Sporadic.Recognition.LyonsFinalCore107
import Certificates.Certificate6114
import Certificates.Kernel.LyBase.FamFacts
import Certificates.Kernel.LyGlue.Bind
public import CFSG.Sporadic.Recognition.LyonsModelCert

public section

open CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition.LyonsSims.LyFinal

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.LyonsSims.LyFinal in
theorem certificate6116 : (∀ r ∈ RB, r ∈ modularR Rcore107 modularD) ∧
    ∀ r ∈ Rcore107 ++ modularLearned ++ dist2BWords, FamRel eEvCore trEvCore r :=
  ⟨fun r hr => List.mem_append_left _ (List.mem_append_left _ (KernelLyBase.rb_mem_core r hr)),
    KernelLyBase.famRel_rfam (KernelLy.cL_eq Ly0.tabCheck_eq_true)
      (KernelLy.dL_eq Ly0.tabCheck_eq_true) certificate6114⟩

end Certificates
