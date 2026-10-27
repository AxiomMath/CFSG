module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag

public section

namespace CFSG.RankThree.PartTwo.Sec12

open Matrix

namespace Hering129KN5

variable {K : Type} [Field K]

theorem of_matrix {π : Bool} {p f : ℕ} (hK : Sec4.PiField π p f K) {τ : K} (hτ : τ ^ 3 = 1)
    {a b c : Kˣ} (M : Matrix (Fin 3) (Fin 3) K) (hMM : M * M = 1) (hdet : M.det = 1)
    (hT : Mᵀ = M) (hfix : ∀ φ : K →+* K, M.map φ = M)
    (hcomm : M * diagonal ![(a : K), b, c] = diagonal ![(a : K), b, c] * M) (l : Kˣ)
    (hconj : M * !![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1] * M =
      Matrix.scalar (Fin 3) (l : K) * !![τ ^ 2, 0, 0; 0, τ, 0; 0, 0, 1]) :
    ∃ t : GL (Fin 3) K, t ∈ Sec4.slPi π 3 (p ^ f) K ∧ t * t = 1 ∧
      t * Sec4.diagUnits a b c = Sec4.diagUnits a b c * t ∧
      ∃ l : Kˣ, t * Sec4.diagTau hτ * t⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) l * (Sec4.diagTau hτ)⁻¹ := by
  refine ⟨⟨M, M, hMM, hMM⟩, ?_, Units.ext hMM, Units.ext hcomm, l, Units.ext ?_⟩
  · cases π
    · rw [Sec4.mem_slPi_false hK.unitary]
      refine ⟨hdet, ?_⟩
      change (M.map _)ᵀ * M = 1
      rw [hfix, hT, hMM]
    · rw [Sec4.mem_slPi_true]
      exact hdet
  · rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact hconj

end Hering129KN5

theorem exists_negPerm {K : Type} [Field K] {p f : ℕ} {π : Bool} (hK : Sec4.PiField π p f K)
    (hq : Sec4.ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {a b c e : Kˣ}
    (hshape : (a = e ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = e ∧ c = 1) ∨ (a = 1 ∧ b = 1 ∧ c = e)) :
    ∃ t : GL (Fin 3) K, t ∈ Sec4.slPi π 3 (p ^ f) K ∧ t * t = 1 ∧
      t * Sec4.diagUnits a b c = Sec4.diagUnits a b c * t ∧
      ∃ l : Kˣ, t * Sec4.diagTau hτ * t⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) l * (Sec4.diagTau hτ)⁻¹ := by
  have h3 : τ * τ ^ 2 = 1 := by rw [← pow_succ']; exact hτ
  have h3' : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ
  have h4 : τ ^ 2 * τ ^ 2 = τ := by linear_combination τ * hτ
  have h2 : τ * τ = τ ^ 2 := (sq τ).symm
  rcases hshape with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    refine Hering129KN5.of_matrix hK hτ !![-1, 0, 0; 0, 0, -1; 0, -1, 0] ?_ ?_ ?_ ?_ ?_
      ⟨τ ^ 2, τ, h3', h3⟩ ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]
    · rw [det_fin_three]; simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · intro φ; ext i j; fin_cases i <;> fin_cases j <;> simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h2, h3, h3', h4]
  ·
    refine Hering129KN5.of_matrix hK hτ !![0, 0, -1; 0, -1, 0; -1, 0, 0] ?_ ?_ ?_ ?_ ?_
      ⟨τ, τ ^ 2, h3, h3'⟩ ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]
    · rw [det_fin_three]; simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · intro φ; ext i j; fin_cases i <;> fin_cases j <;> simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h2, h3, h3', h4]
  ·
    refine Hering129KN5.of_matrix hK hτ !![0, -1, 0; -1, 0, 0; 0, 0, -1] ?_ ?_ ?_ ?_ ?_ 1 ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]
    · rw [det_fin_three]; simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · intro φ; ext i j; fin_cases i <;> fin_cases j <;> simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

end CFSG.RankThree.PartTwo.Sec12
