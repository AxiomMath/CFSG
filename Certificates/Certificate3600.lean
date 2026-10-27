module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Elt
import Certificates.Kernel.UnitarySix.Sec3.Sound.Elt3600
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Chain

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelU6.Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.Monster.B.Co2 in
theorem certificate3600 : (tabsCheck = true)
    ∧ (chS.ok = true)
    ∧ (chS.order = 32768)
    ∧ (chX1.ok = true)
    ∧ (chX1.order = 4)
    ∧ (chX2.ok = true)
    ∧ (chX2.order = 4)
    ∧ (chX3.ok = true)
    ∧ (chX3.order = 2)
    ∧ (chK1.ok = true)
    ∧ (chK1.order = 25920)
    ∧ (chK2.ok = true)
    ∧ (chK2.order = 20160)
    ∧ (chA1.ok = true)
    ∧ (chA1.order = 512)
    ∧ (chA2.ok = true)
    ∧ (chA2.order = 512)
    ∧ (chK1A1.ok = true)
    ∧ (chK1A1.order = 13271040)
    ∧ (chK2A2.ok = true)
    ∧ (chK2A2.order = 10321920)
    ∧ (chL.ok = true)
    ∧ (chL.order = 9196830720)
    ∧ (chB12.ok = true)
    ∧ (chB12.order = 60)
    ∧ (chB23.ok = true)
    ∧ (chB23.order = 60)
    ∧ (chSJ.ok = true)
    ∧ (chSJ.order = 98304)
    ∧ (chT1.ok = true)
    ∧ (chT1.order = 64)
    ∧ (chT2.ok = true)
    ∧ (chT2.order = 64)
    ∧ (validCheck = true)
    ∧ (uNormCheck = true)
    ∧ (kNormCheck = true)
    ∧ (sNormCheck = true)
    ∧ (CFSG.EvenSmallLie.UnitarySix.YamadaSec3.fixCheck = true)
    ∧ (sIntFix = true)
    ∧ (labT1Check = true)
    ∧ (t1K1Check = true)
    ∧ (∀ x ∈ chS.grp, ∃ a, Rep 693 a x ∧ sIntAt a = true)
    ∧ (∀ x ∈ chT2.grp, ∃ a, Rep 693 a x ∧ t2IntAt a = true)
    ∧ (∀ x ∈ chT1.grp, ∃ a, Rep 693 a x ∧ t1IntAt a = true)
    ∧ (∀ x ∈ chA1.grp, ∃ a, Rep 693 a x ∧ ka1At a = true)
    ∧ (∀ x ∈ chA2.grp, ∃ a, Rep 693 a x ∧ ka2At a = true)
    ∧ (∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ normAt a = true) :=
  ⟨tabs_k, chS_k'.1, chS_k'.2, chX1_k'.1, chX1_k'.2, chX2_k'.1, chX2_k'.2, chX3_k'.1, chX3_k'.2,
    chK1_k'.1, chK1_k'.2, chK2_k'.1, chK2_k'.2, chA1_k'.1, chA1_k'.2, chA2_k'.1, chA2_k'.2,
    chK1A1_k'.1, chK1A1_k'.2, chK2A2_k'.1, chK2A2_k'.2, chL_k'.1, chL_k'.2, chB12_k'.1,
    chB12_k'.2, chB23_k'.1, chB23_k'.2, chSJ_k'.1, chSJ_k'.2, chT1_k'.1, chT1_k'.2, chT2_k'.1,
    chT2_k'.2, valid_k, uNorm_k', kNorm_k', sNorm_k', fix_k, sIntFix_k, labT1_k, t1K1_k', sInt_k',
    t2Int_k', t1Int_k', ka1_k', ka2_k', norm_k'⟩

end Certificates
