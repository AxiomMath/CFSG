module

public import Certificates.Data.HeNormWords
import Certificates.Kernel.LocalComp.HeNormGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.HeldFix in
theorem certificate7136 : (∀ w ∈ HeNorm.words, ∀ j ∈ w, j < 9) ∧
    (∀ i < 8, (HeNorm.wti i).size = 8330 ∧ comp 8330 (HeNorm.wti i) (HeNorm.wt i) = idTab 8330) ∧
    (∀ i < 8, ∀ j < 8,
      (HeNorm.hTi i j).size = 8330 ∧ comp 8330 (HeNorm.hTi i j) (HeNorm.hT i j) = idTab 8330) ∧
    ∀ i < 8, ∀ j < 8, i ≠ j → ∃ k < 5, notInOK hfTEnum32.tabs (hfRes (HeNorm.cj i j k)) = true := KernelLC.HeNorm.check

end Certificates

end
