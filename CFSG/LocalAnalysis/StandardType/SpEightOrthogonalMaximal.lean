module

public import CFSG.LocalAnalysis.StandardType.SpEightSingularTransitivity
public import CFSG.LocalAnalysis.StandardType.SpEightSymplecticGeneration

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.Blueprint.EvenSource

theorem Q0_zero : Q0 0 = 0 := by
  have h := Q0_add 0 0
  rw [add_zero, omega_self] at h
  simpa using h

theorem exists_nonsingular_to_singular {g : GL Idx (ZMod 2)} (hgO : g ∉ matrixOrthogonal Q0) :
    ∃ h : GL Idx (ZMod 2), (h = g ∨ h = g⁻¹) ∧ ∃ w : Vec, Q0 w = 1 ∧
      Q0 ((h : Matrix Idx Idx (ZMod 2)) *ᵥ w) = 0 := by
  obtain ⟨v, hv⟩ : ∃ v, Q0 ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v) ≠ Q0 v := by
    by_contra hcon
    push Not at hcon
    exact hgO hcon
  have hval : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hval (Q0 v) with hv0 | hv1
  · rcases hval (Q0 ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v)) with hg0 | hg1
    · exact absurd (hg0.trans hv0.symm) hv
    · refine ⟨g⁻¹, Or.inr rfl, (g : Matrix Idx Idx (ZMod 2)) *ᵥ v, hg1, ?_⟩
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, hv0]
  · rcases hval (Q0 ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v)) with hg0 | hg1
    · exact ⟨g, Or.inl rfl, v, hv1, hg0⟩
    · exact absurd (hg1.trans hv1.symm) hv

theorem eq_statedSp_of_matrixOrthogonal_le {Y : Subgroup (GL Idx (ZMod 2))}
    (hOY : matrixOrthogonal Q0 ≤ Y) (hY : Y ≤ StatedSp 4 (ZMod 2))
    (hne : Y ≠ matrixOrthogonal Q0) : Y = StatedSp 4 (ZMod 2) := by
  have hOSp : matrixOrthogonal Q0 ≤ StatedSp 4 (ZMod 2) := matrixOrthogonal_le_statedSp
  obtain ⟨g, hgY, hgO⟩ : ∃ g ∈ Y, g ∉ matrixOrthogonal Q0 := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hcon hOY)
  obtain ⟨h, hh, w, hw1, hw0⟩ := exists_nonsingular_to_singular hgO
  have hhY : h ∈ Y := by
    rcases hh with rfl | rfl
    · exact hgY
    · exact Y.inv_mem hgY
  have hhSp : h ∈ StatedSp 4 (ZMod 2) := hY hhY
  have htw : tvGL w ∈ Y := hOY (tvGL_mem_matrixOrthogonal hw1)
  have hts : tvGL ((h : Matrix Idx Idx (ZMod 2)) *ᵥ w) ∈ Y := by
    rw [← mul_tvGL_mul_inv hhSp w]
    exact Y.mul_mem (Y.mul_mem hhY htw) (Y.inv_mem hhY)
  have hs0 : (h : Matrix Idx Idx (ZMod 2)) *ᵥ w ≠ 0 := by
    intro h0
    have hw : w = 0 := by
      have := congrArg (fun x => ((h⁻¹ : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *ᵥ x) h0
      simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
    rw [hw, Q0_zero] at hw1
    exact absurd hw1 (by decide)
  have hall : ∀ v : Vec, v ≠ 0 → tvGL v ∈ Y := by
    intro v hv
    by_cases hQ : Q0 v = 1
    · exact hOY (tvGL_mem_matrixOrthogonal hQ)
    · have hQ0 : Q0 v = 0 := by
        generalize Q0 v = c at hQ
        revert c
        decide
      obtain ⟨o, ho, hov⟩ := exists_mem_matrixOrthogonal_mulVec_eq hw0 hQ0 hs0 hv
      rw [← hov, ← mul_tvGL_mul_inv (hOSp ho)]
      exact Y.mul_mem (Y.mul_mem (hOY ho) hts) (Y.inv_mem (hOY ho))
  apply le_antisymm hY
  rw [statedSp_eq_closure_tvGL]
  exact (Subgroup.closure_le _).2 (by
    rintro _ ⟨v, hv, rfl⟩
    exact hall v hv)

end CFSG.StandardType.SpEight
