module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutElt
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Chain
import Certificates.Kernel.UnitarySix.Sec3.Sound.Elt3920

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelU6.Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaHAut CFSG.EvenSmallLie.UnitarySix.YamadaSec3 in
open CFSG.Monster.B.Co2 in
theorem certificate3920 : (basicCheck = true)
    ∧ (normLCheck = true)
    ∧ (outerCheck = true)
    ∧ (normObjCheck = true)
    ∧ (letterCheck = true)
    ∧ (∀ x ∈ chA4.grp, ∃ a, Rep 693 a x ∧ l1At a = true)
    ∧ (∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ p4At a = true)
    ∧ (labA4Check = true) :=
  ⟨basic_k, normL_k', outer_k', normObj_k', letter_k, l1_k', p4_k', labA4_k⟩

end Certificates
