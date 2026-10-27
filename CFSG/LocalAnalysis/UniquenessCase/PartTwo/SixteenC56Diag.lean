module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open scoped Matrix MatrixGroups

namespace OmegaEig

variable {K : Type} [Field K]

@[expose] abbrev quad (v : OmI → K) : K := StatedQuadPlus 2 K v

theorem quad_eq (v : OmI → K) :
    quad v = v (Sum.inl 0) * v (Sum.inr 0) + v (Sum.inl 1) * v (Sum.inr 1) := by
  simp [quad, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two]

@[expose] def pol (v w : OmI → K) : K := quad (v + w) - quad v - quad w

theorem pol_eq (v w : OmI → K) :
    pol v w = v (Sum.inl 0) * w (Sum.inr 0) + w (Sum.inl 0) * v (Sum.inr 0) +
      v (Sum.inl 1) * w (Sum.inr 1) + w (Sum.inl 1) * v (Sum.inr 1) := by
  simp only [pol, quad_eq, Pi.add_apply]
  ring

theorem pol_comm (v w : OmI → K) : pol v w = pol w v := by
  simp only [pol_eq]
  ring

theorem pol_add_right (v w w' : OmI → K) : pol v (w + w') = pol v w + pol v w' := by
  simp only [pol_eq, Pi.add_apply]
  ring

theorem pol_add_left (v v' w : OmI → K) : pol (v + v') w = pol v w + pol v' w := by
  simp only [pol_eq, Pi.add_apply]
  ring

theorem pol_smul_right (t : K) (v w : OmI → K) : pol v (t • w) = t * pol v w := by
  simp only [pol_eq, Pi.smul_apply, smul_eq_mul]
  ring

theorem pol_smul_left (t : K) (v w : OmI → K) : pol (t • v) w = t * pol v w := by
  simp only [pol_eq, Pi.smul_apply, smul_eq_mul]
  ring

theorem pol_zero_right (v : OmI → K) : pol v 0 = 0 := by
  simp [pol_eq]

theorem pol_sum_right {ι : Type*} (v : OmI → K) (s : Finset ι) (w : ι → OmI → K) :
    pol v (∑ i ∈ s, w i) = ∑ i ∈ s, pol v (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pol_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pol_add_right, ih]

theorem quad_smul (t : K) (v : OmI → K) : quad (t • v) = t ^ 2 * quad v := by
  simp only [quad_eq, Pi.smul_apply, smul_eq_mul]
  ring

theorem quad_add (v w : OmI → K) : quad (v + w) = quad v + quad w + pol v w := by
  unfold pol
  ring

theorem pol_self [CharP K 2] (v : OmI → K) : pol v v = 0 := by
  rw [pol_eq]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (v (Sum.inl 0) * v (Sum.inr 0) + v (Sum.inl 1) * v (Sum.inr 1)) * h2

theorem eq_zero_of_pol_eq_zero {v : OmI → K} (h : ∀ w, pol v w = 0) : v = 0 := by
  have h1 := h (Pi.single (Sum.inr 0) 1)
  have h2 := h (Pi.single (Sum.inl 0) 1)
  have h3 := h (Pi.single (Sum.inr 1) 1)
  have h4 := h (Pi.single (Sum.inl 1) 1)
  simp [pol_eq] at h1 h2 h3 h4
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [h1, h2, h3, h4]

@[expose] noncomputable def diagGL : (OmI → Kˣ) →* GL OmI K :=
  (Units.map (Matrix.diagonalRingHom OmI K : (OmI → K) →+* Matrix OmI OmI K).toMonoidHom).comp
    MulEquiv.piUnits.symm.toMonoidHom

theorem coe_diagGL (d : OmI → Kˣ) :
    ((diagGL d : GL OmI K) : Matrix OmI OmI K) = Matrix.diagonal (fun i => (d i : K)) := by
  rfl

theorem diagGL_mulVec (d : OmI → Kˣ) (v : OmI → K) :
    ((diagGL d : GL OmI K) : Matrix OmI OmI K) *ᵥ v = fun i => (d i : K) * v i := by
  funext i
  rw [coe_diagGL, Matrix.mulVec_diagonal]

@[expose] def diagVals (l m : Kˣ) : OmI → Kˣ := Sum.elim ![1, l] ![l * m, m]

@[expose] def torusVals (α β : Kˣ) : OmI → Kˣ := Sum.elim ![α, β] ![α⁻¹, β⁻¹]

end OmegaEig

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
