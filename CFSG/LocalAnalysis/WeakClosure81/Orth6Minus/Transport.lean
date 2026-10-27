module

public import CFSG.LocalAnalysis.WeakClosure81.Orth6Minus.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Orth6Minus

open Matrix CFSG.ClassicalGroups.Orthogonal

private lemma three_eq_zero {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = 3) :
    (3 : F) = 0 := by
  have h := FiniteField.cast_card_eq_zero (K := F)
  rwa [hF] at h

private lemma eq_zero_or_eq_one_or_eq_neg_one {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 3) (x : F) : x = 0 ∨ x = 1 ∨ x = -1 := by
  classical
  have h3 : (3 : F) = 0 := three_eq_zero hF
  have h2 : (2 : F) = -1 := by linear_combination h3
  have h0 : (0 : F) ≠ 1 := zero_ne_one
  have h0' : (0 : F) ≠ -1 := fun h => one_ne_zero (neg_eq_zero.mp h.symm)
  have h1' : (1 : F) ≠ -1 := by
    intro h
    have h2z : (2 : F) = 0 := by linear_combination h
    rw [h2] at h2z
    exact one_ne_zero (neg_eq_zero.mp h2z)
  have hset : ({0, 1, -1} : Finset F) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_triple_eq_three_iff.mpr ⟨h0, h0', h1'⟩, hF]
  have hx : x ∈ ({0, 1, -1} : Finset F) := by
    rw [hset]
    exact Finset.mem_univ x
  simpa using hx

private lemma coeff_eq_one_add_sq {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = 3)
    {b c : F} (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : c = 1 + b ^ 2 := by
  have h3 : (3 : F) = 0 := three_eq_zero hF
  rcases eq_zero_or_eq_one_or_eq_neg_one hF b with rfl | rfl | rfl <;>
    rcases eq_zero_or_eq_one_or_eq_neg_one hF c with rfl | rfl | rfl
  · exfalso; exact hbc 0 (by norm_num)
  · norm_num
  · exfalso; exact hbc 1 (by norm_num)
  · exfalso; exact hbc 0 (by norm_num)
  · exfalso; exact hbc 1 (by linear_combination h3)
  · linear_combination -h3
  · exfalso; exact hbc 0 (by norm_num)
  · exfalso; exact hbc (-1) (by linear_combination h3)
  · linear_combination -h3

private def coordEquiv : Fin 6 ≃ Six where
  toFun := ![Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inl 1, Sum.inr (Sum.inl 1),
    Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)]
  invFun := Sum.elim (![0, 2] : Fin 2 → Fin 6)
    (Sum.elim (![1, 3] : Fin 2 → Fin 6) (![4, 5] : Fin 2 → Fin 6))
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    rintro (i | i | i) <;> fin_cases i <;> rfl

private def transportMat {F : Type*} [Field F] (b : F) : Matrix (Fin 6) (Fin 6) F :=
  !![1, 0, 1, 1, 0, 0;
     1, 0, -1, -1, 0, 0;
     0, 1, 1, -1, 0, 0;
     0, 1, -1, 1, 0, 0;
     0, 0, 0, 0, 1, b;
     0, 0, 0, 0, 0, 1]

private def transportMatInv {F : Type*} [Field F] (b : F) : Matrix (Fin 6) (Fin 6) F :=
  !![-1, -1, 0, 0, 0, 0;
     0, 0, -1, -1, 0, 0;
     1, -1, 1, -1, 0, 0;
     1, -1, -1, 1, 0, 0;
     0, 0, 0, 0, 1, -b;
     0, 0, 0, 0, 0, 1]

private lemma transportMat_mul_transportMatInv {F : Type*} [Field F] (h3 : (3 : F) = 0)
    (b : F) : transportMat b * transportMatInv b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transportMat, transportMatInv, Matrix.mul_apply, Fin.sum_univ_six]
  all_goals linear_combination -h3

private lemma minusQuadForm_comp_coordEquiv {F : Type*} [Field F] (b c : F) (w : Fin 6 → F) :
    CFSG.PGLModel.minusQuadForm 2 b c (w ∘ coordEquiv.symm) =
      w 0 * w 1 + w 2 * w 3 + w 4 ^ 2 + b * w 4 * w 5 + c * w 5 ^ 2 := by
  simp [CFSG.PGLModel.minusQuadForm, CFSG.MatrixModel.minusQuadCore, coordEquiv,
    Fin.sum_univ_two]

private lemma form_transportMat {F : Type*} [Field F] {b c : F} (h3 : (3 : F) = 0)
    (hcq : c = 1 + b ^ 2) (a : Fin 6 → F) :
    (transportMat b *ᵥ a) 0 * (transportMat b *ᵥ a) 1 +
        (transportMat b *ᵥ a) 2 * (transportMat b *ᵥ a) 3 +
        (transportMat b *ᵥ a) 4 ^ 2 +
        b * (transportMat b *ᵥ a) 4 * (transportMat b *ᵥ a) 5 +
        c * (transportMat b *ᵥ a) 5 ^ 2 = ∑ i : Fin 6, a i * a i := by
  rw [hcq]
  simp [transportMat, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  linear_combination (-(a 2) ^ 2 - (a 3) ^ 2 + b * a 4 * a 5 + b ^ 2 * a 5 ^ 2) * h3

theorem exists_minusQuadForm_mulVec_eq_sumSqForm {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 3) {b c : F} (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∃ P : GL Six F, ∀ v : Six → F,
      CFSG.PGLModel.minusQuadForm 2 b c ((P : Matrix Six Six F) *ᵥ v) = sumSqForm v := by
  letI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  have h3 : (3 : F) = 0 := three_eq_zero hcard
  have hcq : c = 1 + b ^ 2 := coeff_eq_one_add_sq hcard hbc
  have hMM' : transportMat b * transportMatInv b = 1 := transportMat_mul_transportMatInv h3 b
  have hPunit : IsUnit (Matrix.reindex coordEquiv coordEquiv (transportMat b)) := by
    refine IsUnit.of_mul_eq_one (Matrix.reindex coordEquiv coordEquiv (transportMatInv b)) ?_
    have hm := map_mul (Matrix.reindexRingEquiv F coordEquiv) (transportMat b) (transportMatInv b)
    rw [hMM', map_one] at hm
    simpa using hm.symm
  let P : GL Six F := hPunit.unit
  refine ⟨P, fun v => ?_⟩
  have hPcoe : (P : Matrix Six Six F) =
      Matrix.reindex coordEquiv coordEquiv (transportMat b) := hPunit.unit_spec
  rw [hPcoe, Matrix.reindex_apply]
  have hv : (transportMat b).submatrix coordEquiv.symm coordEquiv.symm *ᵥ v =
      (transportMat b *ᵥ (v ∘ coordEquiv)) ∘ coordEquiv.symm :=
    Matrix.submatrix_mulVec_equiv (transportMat b) v coordEquiv.symm coordEquiv.symm
  rw [hv, minusQuadForm_comp_coordEquiv, form_transportMat h3 hcq]
  rw [sumSqForm, dotProduct]
  exact Equiv.sum_comp coordEquiv (fun i : Six => v i * v i)

end CFSG.LocalAnalysis.WeakClosure81.Orth6Minus
