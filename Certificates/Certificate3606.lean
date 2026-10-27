module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HAElt
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Chain
import Certificates.Kernel.UnitarySix.Sec3.Sound.Elt3606

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelU6.Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.Monster.B.Co2 in
theorem certificate3606 : (∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ c10At a = true)
    ∧ (∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ c8At a = true)
    ∧ (∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ c11bAt a = true)
    ∧ (labA1Check = true)
    ∧ (∀ x ∈ chZ2S.grp, ∃ a, Rep 693 a x ∧ z2sKeyAt a = true) :=
  ⟨c10_k', c8_k', c11b_k', labA1_k, z2sKey_k'⟩

end Certificates
