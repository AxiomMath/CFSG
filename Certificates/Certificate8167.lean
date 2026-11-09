module

public import CFSG.RankThree.PartTwo.KFacts.KS21U34CheckInputs
public import CFSG.GH74.KGroups.FieldGF
import all CFSG.GH74.KGroups.FieldGF
import all CFSG.RankThree.PartTwo.KFacts.KS21U34CheckInputs

public section

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U34 CFSG.GH74.KGroups Matrix

namespace CertificateChecks.Batch8167

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U34 CFSG.GH74.KGroups Matrix

set_option maxHeartbeats 0 in
private theorem u34_t0 : t0Mat * t0Mat * t0Mat = 1 ∧ t0Mat ≠ 1 ∧ IsGU3 t0Mat ∧ det3 t0Mat = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem u34_A : CheckA := by decide +kernel

set_option maxHeartbeats 0 in
theorem gf16_comm_cancel : ∀ u w t : GF16, u * w + t + w * u = t := by decide +kernel

theorem e02_eq (a u v w y : GF16) : e02 a u v w y = v * (a * y) := by
  unfold e02
  exact gf16_comm_cancel u w _

set_option maxHeartbeats 0 in
theorem cube_cases : ∀ a : GF16, a * a * a = 1 → a = 1 ∨ a = om ∨ a = om * om := by decide +kernel

set_option maxHeartbeats 0 in
private theorem u34_Bv0 : ∀ y z : GF16, e11 (1) z 0 y = 1 → ∀ u w : GF16, e00 (1) u 0 w y = 1 →
    commMat (1) u 0 w y z * commMat (1) u 0 w y z = 1 → commMat (1) u 0 w y z ≠ 1 →
      IsGU3 (commMat (1) u 0 w y z) → InK0 (commMat (1) u 0 w y z) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem u34_By0 : ∀ v z : GF16, e11 (1) z v 0 = 1 → ∀ u w : GF16, e00 (1) u v w 0 = 1 →
    commMat (1) u v w 0 z * commMat (1) u v w 0 z = 1 → commMat (1) u v w 0 z ≠ 1 →
      IsGU3 (commMat (1) u v w 0 z) → InK0 (commMat (1) u v w 0 z) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem u34_Bv1 : ∀ y z : GF16, e11 (om) z 0 y = 1 → ∀ u w : GF16, e00 (om) u 0 w y = 1 →
    commMat (om) u 0 w y z * commMat (om) u 0 w y z = 1 → commMat (om) u 0 w y z ≠ 1 →
      IsGU3 (commMat (om) u 0 w y z) → InK0 (commMat (om) u 0 w y z) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem u34_By1 : ∀ v z : GF16, e11 (om) z v 0 = 1 → ∀ u w : GF16, e00 (om) u v w 0 = 1 →
    commMat (om) u v w 0 z * commMat (om) u v w 0 z = 1 → commMat (om) u v w 0 z ≠ 1 →
      IsGU3 (commMat (om) u v w 0 z) → InK0 (commMat (om) u v w 0 z) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem u34_Bv2 : ∀ y z : GF16, e11 (om * om) z 0 y = 1 → ∀ u w : GF16, e00 (om * om) u 0 w y = 1 →
    commMat (om * om) u 0 w y z * commMat (om * om) u 0 w y z = 1 → commMat (om * om) u 0 w y z ≠ 1 →
      IsGU3 (commMat (om * om) u 0 w y z) → InK0 (commMat (om * om) u 0 w y z) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem u34_By2 : ∀ v z : GF16, e11 (om * om) z v 0 = 1 → ∀ u w : GF16, e00 (om * om) u v w 0 = 1 →
    commMat (om * om) u v w 0 z * commMat (om * om) u v w 0 z = 1 → commMat (om * om) u v w 0 z ≠ 1 →
      IsGU3 (commMat (om * om) u v w 0 z) → InK0 (commMat (om * om) u v w 0 z) := by
  decide +kernel

private theorem u34_B : CheckB := by
  unfold CheckB
  intro a ha z v y h11 u w h02 h00 h1 h2 h3
  have h0 : v * (a * y) = 0 := by rw [← e02_eq a u v w y]; exact h02
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  rcases mul_eq_zero.1 h0 with hv | hay
  · subst hv
    rcases cube_cases a ha with rfl | rfl | rfl
    · exact u34_Bv0 y z h11 u w h00 h1 h2 h3
    · exact u34_Bv1 y z h11 u w h00 h1 h2 h3
    · exact u34_Bv2 y z h11 u w h00 h1 h2 h3
  · have hy : y = 0 := (mul_eq_zero.1 hay).resolve_left ha0
    subst hy
    rcases cube_cases a ha with rfl | rfl | rfl
    · exact u34_By0 v z h11 u w h00 h1 h2 h3
    · exact u34_By1 v z h11 u w h00 h1 h2 h3
    · exact u34_By2 v z h11 u w h00 h1 h2 h3

set_option maxHeartbeats 0 in
private theorem u34_M : CheckM := by decide +kernel

set_option maxHeartbeats 0 in
private theorem u34_Sq : CheckSq := by decide +kernel

set_option maxHeartbeats 0 in
private theorem u34_Block : CheckBlock := by decide +kernel

private theorem u34Facts_0 : U34Facts := ⟨u34_t0, u34_A, u34_B, u34_M, u34_Sq, u34_Block⟩

end CertificateChecks.Batch8167

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U34 CFSG.GH74.KGroups Matrix in
theorem certificate8167 : U34Facts := by
  exact CertificateChecks.Batch8167.u34Facts_0

end Certificates
