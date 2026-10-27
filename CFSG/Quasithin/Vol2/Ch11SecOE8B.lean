module

public import CFSG.Quasithin.Vol2.Ch11SecOE8A
public import CFSG.LinearAlgebra.LinearGroups.Elations

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3

open Matrix CFSG.CGT.Timmesfeld75 CFSG.LinearGroups
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]

abbrev pt (F : Type) [Field F] (i : Fin 3) : Submodule F (Fin 3 → F) :=
  F ∙ (Pi.single i 1 : Fin 3 → F)

omit [Finite F] [CharP F 2] in
theorem finrank_pt (i : Fin 3) : Module.finrank F (pt F i) = 1 :=
  finrank_span_singleton (Pi.single_ne_zero_iff.mpr one_ne_zero)

omit [Finite F] [CharP F 2] in
theorem smul_single (A : SL(3, F)) (j : Fin 3) :
    A • (Pi.single j 1 : Fin 3 → F) = fun i => A i j := by
  ext i
  change ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single j 1) i = A i j
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

omit [Finite F] [CharP F 2] in
theorem entry_of_mem_elation {k : Fin 3} {A : SL(3, F)} (hA : A ∈ elationSubgroup (pt F k)) :
    (∀ i j, i ≠ k → A i j = if i = j then 1 else 0) ∧ ∀ i, A i k = if i = k then 1 else 0 := by
  have hv : (Pi.single k 1 : Fin 3 → F) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  rw [elationSubgroup_eq_lineStab (finrank_pt k)] at hA
  have h1 := (Matrix.SpecialLinearGroup.mem_lineStab_iff A (pt F k)).mp hA
  have h2 := Matrix.SpecialLinearGroup.lineStab_fix_of_span _ hv A hA
  refine ⟨fun i j hik => ?_, fun i => ?_⟩
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h1 (Pi.single j 1))
    have h := congrFun hc i
    rw [smul_single] at h
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_apply, hik, ite_false, smul_zero] at h
    by_cases hij : i = j
    · subst hij
      simp only [ite_true] at h ⊢
      linear_combination -h
    · simp only [hij, ite_false] at h ⊢
      rw [sub_zero] at h
      exact h.symm
  · have h := congrFun h2 i
    rw [smul_single] at h
    simpa [Pi.single_apply] using h

omit [Finite F] [CharP F 2] in
theorem elation_zero_le_stabM : elationSubgroup (pt F 0) ≤ stabM := by
  intro A hA
  obtain ⟨h1, -⟩ := entry_of_mem_elation hA
  exact ⟨by simpa using h1 2 0 (by decide), by simpa using h1 2 1 (by decide)⟩

omit [Finite F] [CharP F 2] in
theorem elation_one_le_stabM : elationSubgroup (pt F 1) ≤ stabM := by
  intro A hA
  obtain ⟨h1, -⟩ := entry_of_mem_elation hA
  exact ⟨by simpa using h1 2 0 (by decide), by simpa using h1 2 1 (by decide)⟩

theorem rho_elation_zero {A : SL(3, F)} (hA : A ∈ elationSubgroup (pt F 0)) :
    rho ⟨A, elation_zero_le_stabM hA⟩ = utriElt (A 0 1) := by
  obtain ⟨h1, h2⟩ := entry_of_mem_elation hA
  have hb : blk A = !![1, A 0 1; 0, 1] := by
    have e00 := h2 0
    have e10 := h2 1
    have e11 := h1 1 1 (by decide)
    simp only [ite_true, show (1 : Fin 3) ≠ 0 by decide, ite_false] at e00 e10 e11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk, e00, e10, e11]
  apply Subtype.ext
  show (sqrtF (blk A).det)⁻¹ • blk A = _
  rw [hb, Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, sqrtF_one, inv_one, one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [utriElt_apply_00, utriElt_apply_01, utriElt_apply_10, utriElt_apply_11]

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3
