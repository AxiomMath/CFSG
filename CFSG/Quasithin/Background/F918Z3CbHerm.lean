module

public import CFSG.Quasithin.Background.F918Z3CbField
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.OrthMinus

open Matrix

section Herm

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] def IsHerm (X : Matrix (Fin 2) (Fin 2) K) : Prop := (X.map σ)ᵀ = X

@[expose] def hAct (P X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  P * X * (P.map σ)ᵀ

abbrev Fx : Type := {x : K // σ x = x}

variable {σ}

theorem IsHerm.apply {X : Matrix (Fin 2) (Fin 2) K} (hX : IsHerm σ X) (i j : Fin 2) :
    σ (X j i) = X i j := by
  have h := congrFun (congrFun hX i) j
  simpa [Matrix.transpose_apply, Matrix.map_apply] using h

theorem isHerm_of_apply {X : Matrix (Fin 2) (Fin 2) K} (h : ∀ i j, σ (X j i) = X i j) :
    IsHerm σ X := by
  ext i j
  simpa [Matrix.transpose_apply, Matrix.map_apply] using h i j

theorem hAct_mul (A B X : Matrix (Fin 2) (Fin 2) K) :
    hAct σ (A * B) X = hAct σ A (hAct σ B X) := by
  unfold hAct
  rw [Matrix.map_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem hAct_one (X : Matrix (Fin 2) (Fin 2) K) : hAct σ 1 X = X := by
  unfold hAct
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one, Matrix.mul_one,
    Matrix.one_mul]

theorem isHerm_hAct (hσσ : ∀ x, σ (σ x) = x) (P : Matrix (Fin 2) (Fin 2) K)
    {X : Matrix (Fin 2) (Fin 2) K} (hX : IsHerm σ X) : IsHerm σ (hAct σ P X) := by
  have hP : (P.map σ).map σ = P := by
    ext i j
    simp [hσσ]
  have e : ((P.map σ)ᵀ).map σ = Pᵀ := by rw [Matrix.transpose_map, hP]
  unfold IsHerm hAct at *
  rw [Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hX]
  simp only [Matrix.mul_assoc]

theorem triple_apply (A X B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (A * X * Bᵀ) i j = A i 0 * X 0 0 * B j 0 + A i 0 * X 0 1 * B j 1 +
      A i 1 * X 1 0 * B j 0 + A i 1 * X 1 1 * B j 1 := by
  simp only [mul_apply, Fin.sum_univ_two, transpose_apply]
  ring

theorem hAct_apply (P X : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    hAct σ P X i j = P i 0 * X 0 0 * σ (P j 0) + P i 0 * X 0 1 * σ (P j 1) +
      P i 1 * X 1 0 * σ (P j 0) + P i 1 * X 1 1 * σ (P j 1) := by
  unfold hAct
  rw [triple_apply]
  rfl

@[expose] def hermEquiv (hσσ : ∀ x, σ (σ x) = x) :
    {X : Matrix (Fin 2) (Fin 2) K // IsHerm σ X} ≃ Fx σ × K × Fx σ where
  toFun X := (⟨X.1 0 0, X.2.apply 0 0⟩, X.1 0 1, ⟨X.1 1 1, X.2.apply 1 1⟩)
  invFun t := ⟨!![t.1.1, t.2.1; σ t.2.1, t.2.2.1], isHerm_of_apply fun i j => by
    fin_cases i <;> fin_cases j <;> simp [hσσ, t.1.2, t.2.2.2]⟩
  left_inv X := by
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X.2.apply 1 0]
  right_inv t := rfl

theorem card_herm (hσσ : ∀ x, σ (σ x) = x) :
    Nat.card {X : Matrix (Fin 2) (Fin 2) K // IsHerm σ X} =
      Nat.card (Fx σ) * (Nat.card K * Nat.card (Fx σ)) := by
  rw [Nat.card_congr (hermEquiv hσσ), Nat.card_prod, Nat.card_prod]

end Herm

section Transvection

variable {K : Type} [Field K] [CharP K 2] {σ : K →+* K}

@[expose] def uSh : Matrix (Fin 2) (Fin 2) K := !![1, 1; 0, 1]

theorem hAct_uSh_eq_iff (X : Matrix (Fin 2) (Fin 2) K) :
    hAct σ uSh X = X ↔ X 1 1 = 0 ∧ X 1 0 = X 0 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have e00 : hAct σ uSh X 0 0 = X 0 0 + X 1 0 + X 0 1 + X 1 1 := by
    rw [hAct_apply]
    simp [uSh]
    ring
  have e01 : hAct σ uSh X 0 1 = X 0 1 + X 1 1 := by
    rw [hAct_apply]
    simp [uSh]
  have e10 : hAct σ uSh X 1 0 = X 1 0 + X 1 1 := by
    rw [hAct_apply]
    simp [uSh]
  have e11 : hAct σ uSh X 1 1 = X 1 1 := by
    rw [hAct_apply]
    simp [uSh]
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    have h00 := congrFun (congrFun h 0) 0
    rw [e01] at h01
    rw [e00] at h00
    have h11 : X 1 1 = 0 := by linear_combination h01
    refine ⟨h11, ?_⟩
    rw [h11] at h00
    rw [← add_eq_zero_iff_eq]
    linear_combination h00
  · rintro ⟨h11, h10⟩
    ext i j
    fin_cases i <;> fin_cases j
    · show hAct σ uSh X 0 0 = X 0 0
      rw [e00]
      linear_combination h10 + h11 + X 0 1 * h2
    · show hAct σ uSh X 0 1 = X 0 1
      rw [e01]
      linear_combination h11
    · show hAct σ uSh X 1 0 = X 1 0
      rw [e10]
      linear_combination h11
    · show hAct σ uSh X 1 1 = X 1 1
      rw [e11]


@[expose] def fixUEquiv :
    {X : Matrix (Fin 2) (Fin 2) K // IsHerm σ X ∧ hAct σ uSh X = X} ≃ Fx σ × Fx σ where
  toFun X := (⟨X.1 0 0, X.2.1.apply 0 0⟩, ⟨X.1 0 1, by
    have h1 := X.2.1.apply 1 0
    have h2 := ((hAct_uSh_eq_iff X.1).mp X.2.2).2
    rw [h2] at h1
    exact h1⟩)
  invFun t := ⟨!![t.1.1, t.2.1; t.2.1, 0], isHerm_of_apply fun i j => by
      fin_cases i <;> fin_cases j <;> simp [t.1.2, t.2.2], (hAct_uSh_eq_iff _).mpr (by simp)⟩
  left_inv X := by
    obtain ⟨X, hX, hXu⟩ := X
    have h := (hAct_uSh_eq_iff X).mp hXu
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h.1, h.2]
  right_inv t := rfl

theorem card_fix_uSh :
    Nat.card {X : Matrix (Fin 2) (Fin 2) K // IsHerm σ X ∧ hAct σ uSh X = X} =
      Nat.card (Fx σ) ^ 2 := by
  rw [Nat.card_congr fixUEquiv, Nat.card_prod, sq]

end Transvection

end CFSG.Quasithin.OrthMinus
