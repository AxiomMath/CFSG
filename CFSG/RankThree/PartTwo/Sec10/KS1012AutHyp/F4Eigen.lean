module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.Finite.Basic

public section

open Polynomial
open scoped Matrix

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

theorem exists_ne_zero_ne_one_of_card_four {K : Type} [Field K] (hK : Nat.card K = 4) :
    ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set K) ⊆ ({0, 1} : Set K) := fun x _ => by
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr (h x hx)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ, hK, Set.ncard_pair zero_ne_one] at h1
  norm_num at h1

theorem pow_three_eq_one_of_card_four {K : Type} [Field K] (hK : Nat.card K = 4) {l : K}
    (hl : l ≠ 0) : l ^ 3 = 1 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one l hl
  rw [← Nat.card_eq_fintype_card, hK] at h
  simpa using h

theorem cube_scalar_eq_one {K : Type} [Field K] (hK : Nat.card K = 4)
    (A : Matrix (Fin 3) (Fin 3) K) (hdet : A.det = 1) (μ : K)
    (hA : A ^ 3 = Matrix.scalar (Fin 3) μ) : μ = 1 := by
  have hμ3 : μ ^ 3 = 1 := by
    have h := congrArg Matrix.det hA
    rw [Matrix.det_pow, hdet, one_pow, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  by_contra hμ1
  set p : K[X] := X ^ 3 - C μ with hp
  have hpm : p.Monic := monic_X_pow_sub_C μ (by norm_num)
  have hpdeg : p.natDegree = 3 := natDegree_X_pow_sub_C
  have hroots : p.roots = 0 := by
    refine Multiset.eq_zero_of_forall_notMem (fun l hl => ?_)
    rw [mem_roots hpm.ne_zero, IsRoot, hp, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hl
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [← hl] at hμ3
      simp at hμ3
    exact hμ1 (hl ▸ pow_three_eq_one_of_card_four hK hl0)
  have hirr : Irreducible p :=
    (hpm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr hroots
  have haeval : aeval A p = 0 := by
    rw [hp, map_sub, map_pow, aeval_X, aeval_C, hA, sub_eq_zero]
    ext i j
    rw [Matrix.scalar_apply, Matrix.algebraMap_matrix_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hmin : p = minpoly K A := minpoly.eq_of_irreducible_of_monic hirr haeval hpm
  have hchar : A.charpoly = p := by
    refine eq_of_monic_of_dvd_of_natDegree_le hpm A.charpoly_monic ?_ ?_
    · rw [hmin]
      exact Matrix.minpoly_dvd_charpoly A
    · rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hpdeg]
  have h := Matrix.det_eq_sign_charpoly_coeff A
  rw [hdet, hchar, hp, Fintype.card_fin, coeff_sub, coeff_X_pow, coeff_C_zero,
    if_neg (by norm_num)] at h
  exact hμ1 (by linear_combination -h)

public theorem exists_eigenvector_of_cube_scalar {K : Type} [Field K] (hK : Nat.card K = 4)
    (A : Matrix (Fin 3) (Fin 3) K) (hdet : A.det = 1) (μ : K)
    (hA : A ^ 3 = Matrix.scalar (Fin 3) μ) :
    ∃ u : Fin 3 → K, u ≠ 0 ∧ ∃ l : K, A.mulVec u = l • u := by
  have hμ := cube_scalar_eq_one hK A hdet μ hA
  subst hμ
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one_of_card_four hK
  have hω3 : ω ^ 3 = 1 := pow_three_eq_one_of_card_four hK hω0
  have hωs : 1 + ω + ω ^ 2 = 0 := by
    have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  let s : K → Matrix (Fin 3) (Fin 3) K := fun c => algebraMap K (Matrix (Fin 3) (Fin 3) K) c
  have hs : ∀ (c : K) (u : Fin 3 → K), (A - s c) *ᵥ u = A *ᵥ u - c • u := fun c u => by
    rw [Matrix.sub_mulVec]
    simp only [s, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  have heig : ∀ (c : K) (u : Fin 3 → K), (A - s c) *ᵥ u = 0 → A *ᵥ u = c • u := fun c u h => by
    rw [hs] at h
    exact sub_eq_zero.mp h
  have hprod : (A - s 1) * ((A - s ω) * (A - s (ω ^ 2))) = 0 := by
    have h1 : (1 : K[X]) + C ω + C ω ^ 2 = 0 := by simpa using congrArg C hωs
    have h3 : (C ω : K[X]) ^ 3 = 1 := by simpa using congrArg C hω3
    have hpoly : (X - C (1 : K)) * ((X - C ω) * (X - C (ω ^ 2))) = X ^ 3 - 1 := by
      rw [C_1, C_pow]
      linear_combination (-(X ^ 2) + X) * h1 + (X - 1) * h3
    have h := congrArg (aeval A) hpoly
    simp only [map_mul, map_sub, map_pow, aeval_X, aeval_C, map_one] at h
    show (A - algebraMap K _ 1) * ((A - algebraMap K _ ω) * (A - algebraMap K _ (ω ^ 2))) = 0
    rw [map_one, map_pow, h, hA, map_one, sub_self]
  set v : Fin 3 → K := Pi.single 0 1 with hv
  have hv0 : v ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [v] at this
  set w₁ := (A - s (ω ^ 2)) *ᵥ v with hw₁
  set w₂ := (A - s ω) *ᵥ w₁ with hw₂
  have hw₃ : (A - s 1) *ᵥ w₂ = 0 := by
    rw [hw₂, hw₁, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, hprod, Matrix.zero_mulVec]
  by_cases h₁ : w₁ = 0
  · exact ⟨v, hv0, ω ^ 2, heig _ _ h₁⟩
  by_cases h₂ : w₂ = 0
  · exact ⟨w₁, h₁, ω, heig _ _ h₂⟩
  exact ⟨w₂, h₂, 1, heig _ _ hw₃⟩

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp
