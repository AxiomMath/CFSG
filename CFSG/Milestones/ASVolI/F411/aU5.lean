module

public import CFSG.Milestones.ASVolI.F411.aU4

public section

namespace CFSG.ASVolI

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section U5

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def burnsideF411a_CY (c : K) : Matrix (Fin 2) (Fin 2) K := !![c, 0; 0, 0]

theorem burnsideF411a_CY_herm (h : UnitaryFieldData p f K) {c : K} (hc : c + h.bar c = -1) :
    burnsideF411a_CY c + ((burnsideF411a_CY c).map h.bar)ᵀ =
      -vecMulVec ![1, 0] (fun j => h.bar ((![1, 0] : Fin 2 → K) j)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideF411a_CY, vecMulVec, hc]

theorem burnsideF411a_blockTriangular_U5 {M : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (h10 : M (.inl 1) (.inl 0) = 0) (hz0 : M (.inr (.inl 0)) (.inl 0) = 0)
    (hz1 : M (.inr (.inl 0)) (.inl 1) = 0) (h20 : M (.inr (.inr 1)) (.inl 0) = 0)
    (h21 : M (.inr (.inr 1)) (.inl 1) = 0) (h2z : M (.inr (.inr 1)) (.inr (.inl 0)) = 0)
    (h30 : M (.inr (.inr 0)) (.inl 0) = 0) (h31 : M (.inr (.inr 0)) (.inl 1) = 0)
    (h3z : M (.inr (.inr 0)) (.inr (.inl 0)) = 0) (h32 : M (.inr (.inr 0)) (.inr (.inr 1)) = 0) :
    M.BlockTriangular fullPos := by
  intro a b hab
  rcases a with i | k | i <;> rcases b with j | l | j
  · fin_cases i <;> fin_cases j <;> simp_all
  · have := i.2
    have := l.2
    simp only [fullPos_inl, fullPos_inr_inl] at hab
    omega
  · have := i.2
    have := j.2
    simp only [fullPos_inl, fullPos_inr_inr] at hab
    omega
  · fin_cases k
    fin_cases j <;> simp_all
  · have := k.2
    have := l.2
    simp only [fullPos_inr_inl] at hab
    omega
  · have := k.2
    have := j.2
    simp only [fullPos_inr_inl, fullPos_inr_inr] at hab
    omega
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> fin_cases l <;> simp_all
  · fin_cases i <;> fin_cases j <;> simp_all

theorem burnsideF411a_hypU5_inner_of_fix (h : UnitaryFieldData p f K)
    (α : MulAut (hypPSU h 2 1)) (hα : ∀ x ∈ hypProjUnitriangular h 2 1, α x = x) :
    ∃ g, α = MulAut.conj g := by
  obtain ⟨σ, A, hA, hAg⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.AutSU.exists_isometry_hypPSU_of_two_le h le_rfl
      (by norm_num) α
  have hint := burnsideF411a_hyp_intertwine h (by norm_num) (by norm_num) α hα σ A hAg
  have hodd : ∀ (A₀ C₀ : Matrix (Fin 2) (Fin 2) K) (x₀ : Fin 2 → K),
      CFSG.ClassicalGroups.UnitaryFlag.IsUnitriangular A₀ →
      C₀ + (C₀.map h.bar)ᵀ = -vecMulVec x₀ (fun j => h.bar (x₀ j)) →
      (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) * (oddDiag h A₀ 1 * oddUni h x₀ C₀).map σ =
        (oddDiag h A₀ 1 * oddUni h x₀ C₀) * (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) := by
    intro A₀ C₀ x₀ hA₀ hC₀
    obtain ⟨g, hg, hgm⟩ :=
      (exists_mem_hypUnitriangular_odd_iff (h := h) _).mpr ⟨A₀, C₀, x₀, hA₀, hC₀, rfl⟩
    have := hint g hg
    rwa [hgm] at this
  have hone : CFSG.ClassicalGroups.UnitaryFlag.IsUnitriangular (1 : Matrix (Fin 2) (Fin 2) K) :=
    ⟨fun _ _ hij => one_apply_ne (ne_of_gt hij), fun i => one_apply_eq i⟩
  have hX1 : ∀ t : K, (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *
      (oddDiag h (burnsideF411a_ut t) 1 * oddUni h 0 0).map σ =
      (oddDiag h (burnsideF411a_ut t) 1 * oddUni h 0 0) *
        (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) := fun t =>
    hodd _ _ _ (burnsideF411a_ut_isUnitriangular t) (by ext i j; simp [vecMulVec])
  have hX3 := hodd 1 burnsideF411a_C3 0 hone
    (by rw [burnsideF411a_C3_skew h]; ext i j; simp [vecMulVec])
  have hm1 : h.bar (-1 : K) = -1 := by rw [map_neg, map_one]
  obtain ⟨c, hc⟩ := h.traceLin_surjective ⟨-1, hm1⟩
  have hc' : c + h.bar c = -1 := congrArg Subtype.val hc
  have hY := hodd 1 (burnsideF411a_CY c) ![1, 0] hone (burnsideF411a_CY_herm h hc')
  simp only [oddDiag_mul_oddUni, burnsideF411a_barInvT_ut, burnsideF411a_barInvT_one]
    at hX1 hX3 hY
  have h1 := hX1 1
  generalize hM : (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = M at hX1 h1 hX3 hY hA
  have m10 : M (.inl 1) (.inl 0) = 0 := by
    have e := congrFun (congrFun h1 (.inl 0)) (.inl 0)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_ut] at e
    first | linear_combination e | linear_combination -e
  have mz0 : M (.inr (.inl 0)) (.inl 0) = 0 := by
    have e := congrFun (congrFun h1 (.inr (.inl 0))) (.inl 1)
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
  have mz1 : M (.inr (.inl 0)) (.inl 1) = 0 := by
    have e := congrFun (congrFun hX3 (.inr (.inl 0))) (.inr (.inr 0))
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
  have m2z : M (.inr (.inr 1)) (.inr (.inl 0)) = 0 := by
    have e := congrFun (congrFun hX3 (.inl 0)) (.inr (.inl 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_C3] at e
    first | linear_combination e | linear_combination -e
  have m3z : M (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by
    have e := congrFun (congrFun hX3 (.inl 1)) (.inr (.inl 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_C3] at e
    first | linear_combination e | linear_combination -e
  have d02 : M (.inl 0) (.inl 0) = M (.inr (.inr 1)) (.inr (.inr 1)) := by
    have e := congrFun (congrFun hX3 (.inl 0)) (.inr (.inr 1))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_C3] at e
    first | linear_combination e | linear_combination -e
  have d0z : M (.inl 0) (.inl 0) = M (.inr (.inl 0)) (.inr (.inl 0)) := by
    have e := congrFun (congrFun hY (.inl 0)) (.inr (.inl 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, burnsideF411a_CY] at e
    first
    | linear_combination e + c * m3z
    | linear_combination -e + c * m3z
    | linear_combination e - c * m3z
    | linear_combination -e - c * m3z
  have hna : h.bar (M (.inl 0) (.inl 0)) * M (.inl 0) (.inl 0) = 1 := by
    have e := congrFun (congrFun hA (.inl 0)) (.inr (.inr 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, m10, mz0, m20, m30] at e
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
    (burnsideF411a_blockTriangular_U5 m10 mz0 mz1 m20 m21 m2z m30 m31 m3z m32) (fun x => ?_) hna
  rcases x with i | k | i
  · fin_cases i
    · rfl
    · exact d01.symm
  · fin_cases k
    exact d0z.symm
  · fin_cases i
    · exact (d02.trans d23).symm
    · exact d02.symm

end U5

end CFSG.ASVolI
