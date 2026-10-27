module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSCertInputs

public section

open CFSG.ComponentClassification.GHarris.SCert

namespace CertificateChecks.Batch22603

open CFSG.ComponentClassification.GHarris.SCert

set_option maxHeartbeats 0 in
private theorem comm_inv_X_0 : ∀ u v : SE, u * SE.gen 6 = SE.gen 6 * u →
    v * SE.gen 6 = SE.gen 6 * v →
    u⁻¹ * v⁻¹ * u * v * (u⁻¹ * v⁻¹ * u * v) = 1 → u⁻¹ * v⁻¹ * u * v ≠ 1 →
      u⁻¹ * v⁻¹ * u * v = SE.gen 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem large_cent_X_1 : ∀ w : SE, w * w = 1 → w ≠ 1 → w * SE.gen 6 = SE.gen 6 * w →
    32 ≤ (Finset.univ.filter fun c : SE => c * SE.gen 6 = SE.gen 6 * c ∧ c * w = w * c).card →
    w = SE.gen 0 ∨ w = SE.invRep 1 ∨ w = SE.invRep 1 * SE.gen 0 ∨ w = SE.gen 6 ∨
      w = SE.gen 6 * SE.gen 0 ∨ w = SE.gen 6 * SE.invRep 1 ∨
      w = SE.gen 6 * SE.invRep 1 * SE.gen 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem classes_CXt_2 : ∀ w : SE, w * w = 1 → w * SE.gen 6 = SE.gen 6 * w →
    w * SE.invRep 1 = SE.invRep 1 * w →
    w ≠ 1 → w ≠ SE.gen 0 → w ≠ SE.invRep 1 → w ≠ SE.invRep 1 * SE.gen 0 →
    ∃ s : SE, s⁻¹ * w * s = SE.invRep 5 ∨ s⁻¹ * w * s = SE.invRep 7 ∨
      s⁻¹ * w * s = SE.invRep 8 := by
  decide +kernel

end CertificateChecks.Batch22603

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GHarris.SCert in
theorem certificate22603 :
    (∀ u v : SE, u * SE.gen 6 = SE.gen 6 * u → v * SE.gen 6 = SE.gen 6 * v →
      u⁻¹ * v⁻¹ * u * v * (u⁻¹ * v⁻¹ * u * v) = 1 → u⁻¹ * v⁻¹ * u * v ≠ 1 →
        u⁻¹ * v⁻¹ * u * v = SE.gen 0) ∧
    (∀ w : SE, w * w = 1 → w ≠ 1 → w * SE.gen 6 = SE.gen 6 * w →
      32 ≤ (Finset.univ.filter fun c : SE => c * SE.gen 6 = SE.gen 6 * c ∧ c * w = w * c).card →
      w = SE.gen 0 ∨ w = SE.invRep 1 ∨ w = SE.invRep 1 * SE.gen 0 ∨ w = SE.gen 6 ∨
        w = SE.gen 6 * SE.gen 0 ∨ w = SE.gen 6 * SE.invRep 1 ∨
        w = SE.gen 6 * SE.invRep 1 * SE.gen 0) ∧
    (∀ w : SE, w * w = 1 → w * SE.gen 6 = SE.gen 6 * w → w * SE.invRep 1 = SE.invRep 1 * w →
      w ≠ 1 → w ≠ SE.gen 0 → w ≠ SE.invRep 1 → w ≠ SE.invRep 1 * SE.gen 0 →
      ∃ s : SE, s⁻¹ * w * s = SE.invRep 5 ∨ s⁻¹ * w * s = SE.invRep 7 ∨
        s⁻¹ * w * s = SE.invRep 8) := by
  exact ⟨CertificateChecks.Batch22603.comm_inv_X_0, CertificateChecks.Batch22603.large_cent_X_1, CertificateChecks.Batch22603.classes_CXt_2⟩

end Certificates
