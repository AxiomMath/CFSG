module

public import CFSG.RankThree.GF2n.Smith81.Lin31TwoAlg
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.Adjugate

public section

namespace CFSG.RankThree.GF2n.Smith81

open scoped Matrix

section Plane

variable {F : Type} [Field F]

@[expose] def leftPlane (n₀ : Fin 2 → F) : AddSubgroup (Matrix (Fin 2) (Fin 2) F) where
  carrier := {X | ∃ w : Fin 2 → F, X = Matrix.vecMulVec n₀ w}
  add_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
    exact ⟨w + w', (Matrix.vecMulVec_add n₀ w w').symm⟩
  zero_mem' := ⟨0, (Matrix.vecMulVec_zero n₀).symm⟩
  neg_mem' := by
    rintro _ ⟨w, rfl⟩
    exact ⟨-w, (Matrix.vecMulVec_neg n₀ w).symm⟩

theorem card_leftPlane_le [Finite F] (n₀ : Fin 2 → F) :
    Nat.card (leftPlane n₀) ≤ Nat.card F ^ 2 := by
  have hsurj : Function.Surjective (fun w : Fin 2 → F =>
      (⟨Matrix.vecMulVec n₀ w, w, rfl⟩ : leftPlane n₀)) := by
    rintro ⟨_, w, rfl⟩
    exact ⟨w, rfl⟩
  have h := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at h
  exact h

theorem exists_smul_of_det_eq_zero {u u' : Fin 2 → F} (hu : u ≠ 0)
    (h : u 0 * u' 1 - u 1 * u' 0 = 0) : ∃ c : F, u' = c • u := by
  by_contra hcon
  push Not at hcon
  exact det_ne_zero_of_ne_smul hu hcon h

theorem eq_planeAdd_of_isotropic [Finite F] {u₁ u₂ : Fin 2 → F} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (Δ : AddSubgroup (Matrix (Fin 2) (Fin 2) F)) (hdet : ∀ X ∈ Δ, X.det = 0)
    {n₀ : Fin 2 → F} (hn₀ : n₀ ≠ 0) (hb : Matrix.vecMulVec n₀ u₁ ∈ Δ)
    (hint : ∀ X ∈ Δ, X ∈ planeAdd u₂ → X = 0) (hcard : Nat.card F ^ 2 ≤ Nat.card Δ) :
    Δ = planeAdd u₁ := by
  have hdich : ∀ X ∈ Δ, X ∈ planeAdd u₁ ∨ X ∈ leftPlane n₀ := by
    intro X hX
    by_cases hX0 : X = 0
    · left
      rw [hX0]
      exact zero_mem _
    obtain ⟨a, v, ha, hv, rfl⟩ := exists_vecMulVec_of_det_eq_zero hX0 (hdet X hX)
    have h := hdet _ (add_mem hX hb)
    rw [det_vecMulVec_add] at h
    rcases mul_eq_zero.mp h with h1 | h2
    · right
      obtain ⟨c, hc⟩ := exists_smul_of_det_eq_zero hn₀ (u' := a) (by linear_combination -h1)
      exact ⟨c • v, by rw [hc, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]⟩
    · left
      obtain ⟨c, hc⟩ := exists_smul_of_det_eq_zero hu₁ (u' := v) (by linear_combination -h2)
      exact ⟨c • a, by rw [hc, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]⟩
  have hcase : Δ ≤ planeAdd u₁ ∨ Δ ≤ leftPlane n₀ := by
    rw [← AddSubgroupClass.subset_union]
    intro X hX
    exact hdich X hX
  rcases hcase with h | h
  · exact AddSubgroup.eq_of_le_of_card_ge h (by rw [card_planeAdd hu₁]; exact hcard)
  · exfalso
    have hΔ : Δ = leftPlane n₀ :=
      AddSubgroup.eq_of_le_of_card_ge h ((card_leftPlane_le n₀).trans hcard)
    have hmem : Matrix.vecMulVec n₀ u₂ ∈ Δ := by
      rw [hΔ]
      exact ⟨u₂, rfl⟩
    exact Matrix.vecMulVec_ne_zero hn₀ hu₂ (hint _ hmem (vecMulVec_mem_planeAdd n₀ u₂))

end Plane

section Matrix

variable {F : Type} [Field F]

theorem exists_det_one_mulVec_single {n : Fin 2 → F} (hn : n ≠ 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, P.det = 1 ∧ P *ᵥ ![1, 0] = n := by
  by_cases h0 : n 0 = 0
  · have h1 : n 1 ≠ 0 := fun h1 => hn (by ext k; fin_cases k <;> simp [h0, h1])
    refine ⟨!![0, -(n 1)⁻¹; n 1, 0], ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      field_simp
      ring
    · ext k
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨!![n 0, 0; n 1, (n 0)⁻¹], ?_, ?_⟩
    · rw [Matrix.det_fin_two_of, mul_inv_cancel₀ h0]
      ring
    · ext k
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_det_one_mulVec_eq {n n' : Fin 2 → F} (hn : n ≠ 0) (hn' : n' ≠ 0) :
    ∃ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 ∧ g *ᵥ n = n' := by
  obtain ⟨P, hP, hPn⟩ := exists_det_one_mulVec_single hn
  obtain ⟨P', hP', hPn'⟩ := exists_det_one_mulVec_single hn'
  refine ⟨P' * P.adjugate, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_adjugate, hP, hP']
    simp
  · have h1 : P.adjugate *ᵥ n = ![1, 0] := by
      rw [← hPn, Matrix.mulVec_mulVec, Matrix.adjugate_mul, hP]
      simp
    rw [← Matrix.mulVec_mulVec, h1, hPn']

end Matrix

end CFSG.RankThree.GF2n.Smith81
