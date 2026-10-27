module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XElt
import Certificates.Kernel.UnitarySix.Sec3.Sound.Glue3601
import Certificates.Kernel.UnitarySix.Sec3.Sound.Elt3601
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Chain

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelU6.Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.Monster.B.Co2 in
theorem certificate3601 : (xIdCheck = true)
    ∧ (xCommCheck = true)
    ∧ (xWitCheck = true)
    ∧ (xNormCheck = true)
    ∧ (xFixCheck = true)
    ∧ (chA3.ok = true)
    ∧ (chA3.order = 4096)
    ∧ (chA4.ok = true)
    ∧ (chA4.order = 16)
    ∧ (chX8.ok = true)
    ∧ (chX8.order = 4)
    ∧ (chSig.ok = true)
    ∧ (chSig.order = 6)
    ∧ (chLam.ok = true)
    ∧ (chLam.order = 60)
    ∧ (chZ2S.ok = true)
    ∧ (chZ2S.order = 8)
    ∧ (chX6Z.ok = true)
    ∧ (chX6Z.order = 32)
    ∧ (chZ.ok = true)
    ∧ (chZ.order = 2)
    ∧ (chX1Z.ok = true)
    ∧ (chX1Z.order = 32)
    ∧ (chP2.ok = true)
    ∧ (chP2.order = 1474560)
    ∧ (a1GenCheck = true)
    ∧ (labA3Check = true)
    ∧ (∀ x ∈ chA2.grp, ∃ a, Rep 693 a x ∧ zSAt a = true)
    ∧ (∀ x ∈ chA3.grp, ∃ a, Rep 693 a x ∧ zA3At a = true)
    ∧ (∀ x ∈ chA1.grp, ∃ a, Rep 693 a x ∧ a1At a = true)
    ∧ (∀ x ∈ chA4.grp, ∃ a, Rep 693 a x ∧ a4At a = true)
    ∧ (∀ x ∈ chA4.grp, ∀ y ∈ chX1.grp, ∃ b a, Rep 693 b y ∧ Rep 693 a x ∧ a4PairAt b a = true)
    ∧ (∀ x ∈ chZ2S.grp, ∃ a, Rep 693 a x ∧ z2sAt a = true)
    ∧ (∀ x ∈ chZ2S.grp, ∀ y ∈ chX1.grp, ∃ b a, Rep 693 b y ∧ Rep 693 a x ∧ z2sPairAt b a = true)
    ∧ (∀ x ∈ chA2.grp, ∃ a, Rep 693 a x ∧ a2At a = true)
    ∧ (∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ p2At a = true)
    ∧ (uACheck = true) :=
  ⟨xId_k, xComm_k, xWit_k, xNorm_k', xFix_k, chA3_k'.1, chA3_k'.2, chA4_k'.1, chA4_k'.2,
    chX8_k'.1, chX8_k'.2, chSig_k'.1, chSig_k'.2, chLam_k'.1, chLam_k'.2, chZ2S_k'.1, chZ2S_k'.2,
    chX6Z_k'.1, chX6Z_k'.2, chZ_k'.1, chZ_k'.2, chX1Z_k'.1, chX1Z_k'.2, chP2_k'.1, chP2_k'.2,
    a1Gen_k', labA3_k, zS_k', zA3_k', a1_k', a4_k', a4Pair_k', z2s_k', z2sPair_k', a2_k', p2_k',
    uA_k'⟩

end Certificates
