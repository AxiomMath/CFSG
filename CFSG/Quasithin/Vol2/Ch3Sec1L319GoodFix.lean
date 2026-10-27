module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Recognition.CertOvergroup
public import CFSG.Quasithin.Vol2.Ch3zCoreMod

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Quasithin CFSG.Quasithin.Ch3z

theorem fld_sq_of_fixed {K : Type} [Field K] {a b c d x y : K} (h2 : (2 : K) = 0)
    (hdet : a * d - b * c = 1) (e0 : a * x + b * y = x) (e1 : c * x + d * y = y)
    (hw : x ≠ 0 ∨ y ≠ 0) :
    a * a + b * c = 1 ∧ a * b + b * d = 0 ∧ c * a + d * c = 0 ∧ c * b + d * d = 1 := by
  have hDx : ((a + 1) * (d + 1) - b * c) * x = 0 := by
    linear_combination (d + 1) * e0 - b * e1 + (-(b * y) + (d + 1) * x) * h2
  have hDy : ((a + 1) * (d + 1) - b * c) * y = 0 := by
    linear_combination (a + 1) * e1 - c * e0 + (-(c * x) + (a + 1) * y) * h2
  have hD : (a + 1) * (d + 1) - b * c = 0 := by
    by_contra hD0
    have hx : x = 0 := (mul_eq_zero.mp hDx).resolve_left hD0
    have hy : y = 0 := (mul_eq_zero.mp hDy).resolve_left hD0
    rcases hw with hw | hw
    · exact hw hx
    · exact hw hy
  have hs : a + d = 0 := by linear_combination hD - hdet - h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -hdet + a * hs - h2
  · linear_combination b * hs
  · linear_combination c * hs
  · linear_combination -hdet + d * hs - h2

theorem sl2_sq_eq_one_of_fixed {K : Type} [Field K] [CharP K 2] (γ : Matrix.SpecialLinearGroup (Fin 2) K)
    {w : Fin 2 → K} (hw : w ≠ 0) (hfix : (γ : Matrix (Fin 2) (Fin 2) K).mulVec w = w) : γ ^ 2 = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hdet : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 * (γ : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) K) 0 1 * (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have e0 : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 * w 0 + (γ : Matrix (Fin 2) (Fin 2) K) 0 1 * w 1 = w 0 := by
    have := congrFun hfix 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e1 : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 * w 0 + (γ : Matrix (Fin 2) (Fin 2) K) 1 1 * w 1 = w 1 := by
    have := congrFun hfix 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hwne : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hw
    funext i
    fin_cases i
    · exact hc.1
    · exact hc.2
  obtain ⟨q1, q2, q3, q4⟩ := fld_sq_of_fixed h2 hdet e0 e1 hwne
  have hsq : (γ : Matrix (Fin 2) (Fin 2) K) * (γ : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, q1, q2, q3, q4]
  rw [pow_two]
  exact Subtype.ext (by simpa using hsq)

theorem sl2_eq_one_of_odd_fixed {K : Type} [Field K] [CharP K 2] (γ : Matrix.SpecialLinearGroup (Fin 2) K)
    (hodd : Odd (orderOf γ)) {w : Fin 2 → K} (hw : w ≠ 0)
    (hfix : (γ : Matrix (Fin 2) (Fin 2) K).mulVec w = w) : γ = 1 := by
  have hdvd : orderOf γ ∣ 2 := orderOf_dvd_of_pow_eq_one (sl2_sq_eq_one_of_fixed γ hw hfix)
  have h1 : orderOf γ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

end CFSG.Quasithin.H13.L319
