module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3YElt
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Chain
import Certificates.Kernel.UnitarySix.Sec3.Sound.Elt3602

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelU6.Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.Monster.B.Co2 in
theorem certificate3602 : (∀ x ∈ chA2.grp, ∃ a, Rep 693 a x ∧ a2OrbAt a = true)
    ∧ (∀ x ∈ chA1.grp, ∃ a, Rep 693 a x ∧ a1OrbAt a = true)
    ∧ (∀ x ∈ chA3.grp, ∃ a, Rep 693 a x ∧ a3OrbAt a = true)
    ∧ (∀ x ∈ chA1.grp, ∃ a, Rep 693 a x ∧ singAt a = true)
    ∧ (zClsCheck = true)
    ∧ (chA2s0.ok = true)
    ∧ (chA2s0.order = 512)
    ∧ (chA2s1.ok = true)
    ∧ (chA2s1.order = 512)
    ∧ (chA2s2.ok = true)
    ∧ (chA2s2.order = 512)
    ∧ (chA1s0.ok = true)
    ∧ (chA1s0.order = 512)
    ∧ (chA1s1.ok = true)
    ∧ (chA1s1.order = 512)
    ∧ (chA3s0.ok = true)
    ∧ (chA3s0.order = 4096)
    ∧ (chA3s1.ok = true)
    ∧ (chA3s1.order = 4096)
    ∧ (chA3s2.ok = true)
    ∧ (chA3s2.order = 4096)
    ∧ (chA3s3.ok = true)
    ∧ (chA3s3.order = 4096)
    ∧ (chA3s4.ok = true)
    ∧ (chA3s4.order = 4096)
    ∧ (yKeysCheck = true)
    ∧ (a1RepsCheck = true)
    ∧ (singGenCheck = true) :=
  ⟨a2Orb_k', a1Orb_k', a3Orb_k', sing_k', zCls_k, chA2s0_k'.1, chA2s0_k'.2, chA2s1_k'.1,
    chA2s1_k'.2, chA2s2_k'.1, chA2s2_k'.2, chA1s0_k'.1, chA1s0_k'.2, chA1s1_k'.1, chA1s1_k'.2,
    chA3s0_k'.1, chA3s0_k'.2, chA3s1_k'.1, chA3s1_k'.2, chA3s2_k'.1, chA3s2_k'.2, chA3s3_k'.1,
    chA3s3_k'.2, chA3s4_k'.1, chA3s4_k'.2, yKeys_k, a1Reps_k, singGen_k⟩

end Certificates
