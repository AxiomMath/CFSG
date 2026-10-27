module

public import CFSG.Quasithin.Background.F918Z3CbHerm
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.OrthMinus

open Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem exists_conj_uSh {g : Matrix (Fin 2) (Fin 2) K} (hg : g * g = 1) (hne : g ≠ 1) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) K, P * Q = 1 ∧ Q * P = 1 ∧ g * P = P * uSh := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : K, g = !![p, q; r, s] :=
    ⟨g 0 0, g 0 1, g 1 0, g 1 1, Matrix.eta_fin_two g⟩
  have e00 := congrFun (congrFun hg 0) 0
  have e01 := congrFun (congrFun hg 0) 1
  have e10 := congrFun (congrFun hg 1) 0
  have e11 := congrFun (congrFun hg 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  by_cases hr : r = 0
  · subst hr
    have hp : p = 1 := by
      have : (p + 1) * (p + 1) = 0 := by linear_combination e00 + (p + 1) * h2
      exact (add_eq_zero_iff_eq p 1).mp (mul_self_eq_zero.mp this)
    have hs : s = 1 := by
      have : (s + 1) * (s + 1) = 0 := by linear_combination e11 + (s + 1) * h2
      exact (add_eq_zero_iff_eq s 1).mp (mul_self_eq_zero.mp this)
    subst hp hs
    have hq : q ≠ 0 := by
      rintro rfl
      exact hne Matrix.one_fin_two.symm
    refine ⟨!![q, 0; 0, 1], !![q⁻¹, 0; 0, 1], ?_, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hq]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hq]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, uSh]
  · have hinv : r⁻¹ * r = 1 := inv_mul_cancel₀ hr
    refine ⟨!![p + 1, 1; r, 0], !![0, r⁻¹; 1, r⁻¹ * (p + 1)], ?_, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hr]
      linear_combination (r⁻¹ * (p + 1)) * h2
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hr]
      linear_combination (p + 1) * hinv + (p + 1) * h2
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, uSh] <;>
        first
          | linear_combination e00
          | linear_combination (-1) * h2
          | linear_combination e10


section Fix

variable {σ : K →+* K}

abbrev FixSet (σ : K →+* K) (g : Matrix (Fin 2) (Fin 2) K) : Type :=
  {X : Matrix (Fin 2) (Fin 2) K // IsHerm σ X ∧ hAct σ g X = X}

@[expose] def fixConjEquiv (hσσ : ∀ x, σ (σ x) = x) {g P Q : Matrix (Fin 2) (Fin 2) K}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hgP : g * P = P * uSh) :
    FixSet σ g ≃ FixSet σ uSh :=
  have hQg : Q * g = uSh * Q :=
    calc Q * g = Q * g * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = Q * (g * P) * Q := by simp only [Matrix.mul_assoc]
      _ = Q * (P * uSh) * Q := by rw [hgP]
      _ = (Q * P) * uSh * Q := by simp only [Matrix.mul_assoc]
      _ = uSh * Q := by rw [hQP, Matrix.one_mul]
  { toFun := fun X => ⟨hAct σ Q X.1, isHerm_hAct hσσ Q X.2.1, by
      rw [← hAct_mul, ← hQg, hAct_mul, X.2.2]⟩
    invFun := fun Y => ⟨hAct σ P Y.1, isHerm_hAct hσσ P Y.2.1, by
      rw [← hAct_mul, hgP, hAct_mul, Y.2.2]⟩
    left_inv := fun X => Subtype.ext (by
      show hAct σ P (hAct σ Q X.1) = X.1
      rw [← hAct_mul, hPQ, hAct_one])
    right_inv := fun Y => Subtype.ext (by
      show hAct σ Q (hAct σ P Y.1) = Y.1
      rw [← hAct_mul, hQP, hAct_one]) }

theorem card_fix_sq (hσσ : ∀ x, σ (σ x) = x) (hF : Nat.card (Fx σ) ^ 2 = Nat.card K)
    {g : Matrix (Fin 2) (Fin 2) K} (hg : g * g = 1) (hne : g ≠ 1) :
    Nat.card (FixSet σ g) ^ 2 = Nat.card {X : Matrix (Fin 2) (Fin 2) K // IsHerm σ X} := by
  obtain ⟨P, Q, hPQ, hQP, hgP⟩ := exists_conj_uSh hg hne
  rw [Nat.card_congr (fixConjEquiv hσσ hPQ hQP hgP), card_fix_uSh, card_herm hσσ, ← hF]
  ring

end Fix

end CFSG.Quasithin.OrthMinus
