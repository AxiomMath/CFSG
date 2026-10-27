module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3ZElt
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Chain
import Certificates.Kernel.UnitarySix.Sec3.Sound.Elt3603

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelU6.Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.Monster.B.Co2 in
theorem certificate3603 : (coordNGenCheck = true)
    ∧ (∀ x ∈ chA1.grp, ∃ a, Rep 693 a x ∧ coordNAt a = true)
    ∧ (coordWGenCheck = true)
    ∧ (∀ x ∈ chA4.grp, ∃ a, Rep 693 a x ∧ coordWAt a = true)
    ∧ (∀ x ∈ chA4.grp, ∀ y ∈ chA4.grp, ∃ a b, Rep 693 a x ∧ Rep 693 b y ∧ coordWPairAt a b = true) :=
  ⟨coordNGen_k, coordN_k', coordWGen_k, coordW_k', coordWPair_k'⟩

end Certificates
