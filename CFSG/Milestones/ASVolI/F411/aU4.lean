module

public import CFSG.Milestones.ASVolI.F411.aUCore
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSU

public section

namespace CFSG.ASVolI

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section U4

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def burnsideF411a_ut (t : K) : Matrix (Fin 2) (Fin 2) K := !![1, t; 0, 1]

theorem burnsideF411a_ut_isUnitriangular (t : K) :
    CFSG.ClassicalGroups.UnitaryFlag.IsUnitriangular (burnsideF411a_ut t) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [burnsideF411a_ut]
  · fin_cases i <;> simp [burnsideF411a_ut]

theorem burnsideF411a_barInvT_ut (h : UnitaryFieldData p f K) (t : K) :
    barInvT h (burnsideF411a_ut t) = !![1, 0; -h.bar t, 1] := by
  have hmap : (burnsideF411a_ut t).map h.bar = !![1, h.bar t; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [burnsideF411a_ut]
  have hinv : (!![1, h.bar t; 0, 1] : Matrix (Fin 2) (Fin 2) K)⁻¹ = !![1, -h.bar t; 0, 1] := by
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [barInvT, hmap, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem burnsideF411a_barInvT_one (h : UnitaryFieldData p f K) :
    barInvT h (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [barInvT, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), inv_one, transpose_one]

@[expose] def burnsideF411a_C3 : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

theorem burnsideF411a_C3_skew (h : UnitaryFieldData p f K) :
    burnsideF411a_C3 + ((burnsideF411a_C3 : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideF411a_C3]

theorem burnsideF411a_blockTriangular_U4 {M : Matrix (HypIndex 2 0) (HypIndex 2 0) K}
    (h10 : M (.inl 1) (.inl 0) = 0) (h20 : M (.inr (.inr 1)) (.inl 0) = 0)
    (h30 : M (.inr (.inr 0)) (.inl 0) = 0) (h21 : M (.inr (.inr 1)) (.inl 1) = 0)
    (h31 : M (.inr (.inr 0)) (.inl 1) = 0) (h32 : M (.inr (.inr 0)) (.inr (.inr 1)) = 0) :
    M.BlockTriangular fullPos := by
  intro a b hab
  rcases a with i | k | i
  · rcases b with j | l | j
    · fin_cases i <;> fin_cases j <;> simp_all
    · exact l.elim0
    · have := i.2
      have := j.2
      simp only [fullPos_inl, fullPos_inr_inr] at hab
      omega
  · exact k.elim0
  · rcases b with j | l | j
    · fin_cases i <;> fin_cases j <;> simp_all
    · exact l.elim0
    · fin_cases i <;> fin_cases j <;> simp_all

theorem burnsideF411a_hypU4_inner_of_fix (h : UnitaryFieldData p f K)
    (α : MulAut (hypPSU h 2 0)) (hα : ∀ x ∈ hypProjUnitriangular h 2 0, α x = x) :
    ∃ g, α = MulAut.conj g := by
  obtain ⟨σ, A, hA, hAg⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.AutSU.exists_isometry_hypPSU_of_two_le h le_rfl
      (by norm_num) α
  have hint := burnsideF411a_hyp_intertwine h (by norm_num) (by norm_num) α hα σ A hAg
  have hX1 : ∀ t : K, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (evenMat h (burnsideF411a_ut t) 0).map σ =
      evenMat h (burnsideF411a_ut t) 0 * (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
    intro t
    have hC : (0 : Matrix (Fin 2) (Fin 2) K) + ((0 : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ = 0 := by
      simp
    have := hint _ (evenUnitriangularElt (h := h) (burnsideF411a_ut_isUnitriangular t) hC).2
    rwa [coe_evenUnitriangularElt] at this
  have hX3 : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (evenMat h 1 burnsideF411a_C3).map σ =
      evenMat h 1 burnsideF411a_C3 * (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
    have hone : CFSG.ClassicalGroups.UnitaryFlag.IsUnitriangular (1 : Matrix (Fin 2) (Fin 2) K) :=
      ⟨fun _ _ hij => one_apply_ne (ne_of_gt hij), fun i => one_apply_eq i⟩
    have := hint _ (evenUnitriangularElt (h := h) hone (burnsideF411a_C3_skew h)).2
    rwa [coe_evenUnitriangularElt] at this
  simp only [evenMat, burnsideF411a_barInvT_ut, burnsideF411a_barInvT_one] at hX1 hX3
  have h1 := hX1 1
  generalize hM : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = M at hX1 h1 hX3 hA
  have m10 : M (.inl 1) (.inl 0) = 0 := by
    have e := congrFun (congrFun h1 (.inl 0)) (.inl 0)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_ut] at e
    first | linear_combination e | linear_combination -e
  have m30 : M (.inr (.inr 0)) (.inl 0) = 0 := by
    have e := congrFun (congrFun h1 (.inr (.inr 1))) (.inl 0)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_ut] at e
    first | linear_combination e | linear_combination -e
  have m32 : M (.inr (.inr 0)) (.inr (.inr 1)) = 0 := by
    have e := congrFun (congrFun h1 (.inr (.inr 1))) (.inr (.inr 1))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_ut] at e
    first | linear_combination e | linear_combination -e
  have d01 : M (.inl 0) (.inl 0) = M (.inl 1) (.inl 1) := by
    have e := congrFun (congrFun h1 (.inl 0)) (.inl 1)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_ut] at e
    first | linear_combination e | linear_combination -e
  have d23 : M (.inr (.inr 1)) (.inr (.inr 1)) = M (.inr (.inr 0)) (.inr (.inr 0)) := by
    have e := congrFun (congrFun h1 (.inr (.inr 1))) (.inr (.inr 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_ut] at e
    first | linear_combination e | linear_combination -e
  have m20 : M (.inr (.inr 1)) (.inl 0) = 0 := by
    have e := congrFun (congrFun hX3 (.inl 0)) (.inl 0)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_C3] at e
    first | linear_combination e | linear_combination -e
  have m21 : M (.inr (.inr 1)) (.inl 1) = 0 := by
    have e := congrFun (congrFun hX3 (.inl 0)) (.inl 1)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_C3] at e
    first | linear_combination e | linear_combination -e
  have m31 : M (.inr (.inr 0)) (.inl 1) = 0 := by
    have e := congrFun (congrFun hX3 (.inl 1)) (.inl 1)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_C3] at e
    first | linear_combination e | linear_combination -e
  have d02 : M (.inl 0) (.inl 0) = M (.inr (.inr 1)) (.inr (.inr 1)) := by
    have e := congrFun (congrFun hX3 (.inl 0)) (.inr (.inr 1))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_C3] at e
    first | linear_combination e | linear_combination -e
  have hna : h.bar (M (.inl 0) (.inl 0)) * M (.inl 0) (.inl 0) = 1 := by
    have e := congrFun (congrFun hA (.inl 0)) (.inr (.inr 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, m10, m20, m30] at e
    rw [← d23, ← d02] at e
    exact e
  have ha : M (.inl 0) (.inl 0) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hna
    exact zero_ne_one hna
  have hσt : ∀ t : K, σ t = t := by
    intro t
    have e := congrFun (congrFun (hX1 t) (.inl 0)) (.inl 1)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_ut] at e
    have e2 : M (.inl 0) (.inl 0) * (σ t - t) = 0 := by
      first
      | linear_combination e - t * d01
      | linear_combination -e - t * d01
      | linear_combination e + t * d01
      | linear_combination -e + t * d01
    exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_left ha)
  have hσ : σ = 1 := RingEquiv.ext fun t => by rw [hσt t]; rfl
  subst hM
  refine burnsideF411a_hyp_inner_of_shape h α σ hσ A hA hAg _ ha
    (burnsideF411a_blockTriangular_U4 m10 m20 m30 m21 m31 m32) (fun x => ?_) hna
  rcases x with i | k | i
  · fin_cases i
    · rfl
    · exact d01.symm
  · exact k.elim0
  · fin_cases i
    · exact (d02.trans d23).symm
    · exact d02.symm

end U4

end CFSG.ASVolI
