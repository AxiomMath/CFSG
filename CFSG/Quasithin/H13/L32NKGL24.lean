module

public import CFSG.Quasithin.H13.L32NKG14332

public section

namespace CFSG.Quasithin.H13

open scoped MatrixGroups

theorem exists_sl2F4_mulVec (v : Fin 2 → RuType.F4) (hv : v ≠ 0) :
    ∃ M : SL(2, RuType.F4), (M : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec ![1, 0] = v := by
  by_cases hx : v 0 = 0
  · have hy : v 1 ≠ 0 := by
      intro hy
      apply hv
      ext i
      fin_cases i
      · exact hx
      · exact hy
    refine ⟨⟨!![0, (v 1)⁻¹; v 1, 0], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of, mul_zero, zero_sub, inv_mul_cancel₀ hy]
      decide
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hx]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of, mul_inv_cancel₀ hx, zero_mul, sub_zero]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem kgL24Quad : KGL24Quad := by
  intro q ⟨β, hpol⟩ hinv
  have hconst : ∀ v, v ≠ 0 → q v = q ![1, 0] := by
    intro v hv
    obtain ⟨M, hM⟩ := exists_sl2F4_mulVec v hv
    rw [← hM, hinv]
  have h0 : q 0 = 0 := by
    have h := hpol 0 0
    simp only [add_zero, map_zero] at h
    revert h
    generalize q 0 = x
    decide +revert
  have hne1 : ∀ c : RuType.F4, (![1, 0] + ![0, c] : Fin 2 → RuType.F4) ≠ 0 := by
    intro c h
    have := congrFun h 0
    simp at this
  have hne2 : ∀ c : RuType.F4, c ≠ 0 → (![0, c] : Fin 2 → RuType.F4) ≠ 0 := by
    intro c hc h
    exact hc (by simpa using congrFun h 1)
  have hω0 : RuType.F4.ω ≠ 0 := by decide
  have h1 := hpol ![1, 0] ![0, 1]
  have h2 := hpol ![1, 0] ![0, RuType.F4.ω]
  have h3 := hpol ![1, 0] ![0, 1 + RuType.F4.ω]
  rw [hconst _ (hne1 _), hconst _ (hne2 _ one_ne_zero)] at h1
  rw [hconst _ (hne1 _), hconst _ (hne2 _ hω0)] at h2
  have hω1 : (1 : RuType.F4) + RuType.F4.ω ≠ 0 := by decide
  rw [hconst _ (hne1 _), hconst _ (hne2 _ hω1)] at h3
  have hsplit : (![0, 1 + RuType.F4.ω] : Fin 2 → RuType.F4) = ![0, 1] + ![0, RuType.F4.ω] := by
    ext i
    fin_cases i <;> simp
  rw [hsplit, map_add] at h3
  have hκ : q ![1, 0] = 0 := by
    revert h1 h2 h3
    generalize q ![1, 0] = κ
    generalize β ![1, 0] ![0, 1] = b₁
    generalize β ![1, 0] ![0, RuType.F4.ω] = b₂
    decide +revert
  intro v
  by_cases hv : v = 0
  · rw [hv, h0]
  · rw [hconst v hv, hκ]

end CFSG.Quasithin.H13
