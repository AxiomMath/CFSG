module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinearSU

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.Universal.Unitary

section Form

variable {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}

@[expose] def ggUForm (x y : Fin n → F) : F := ∑ t, σ (x t) * y (Fin.rev t)

theorem ggUForm_def (x y : Fin n → F) : ggUForm σ x y = ∑ t, σ (x t) * y (Fin.rev t) := rfl

theorem ggUForm_add_left (x x' y : Fin n → F) :
    ggUForm σ (x + x') y = ggUForm σ x y + ggUForm σ x' y := by
  simp only [ggUForm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem ggUForm_add_right (x y y' : Fin n → F) :
    ggUForm σ x (y + y') = ggUForm σ x y + ggUForm σ x y' := by
  simp only [ggUForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ggUForm_smul_left (c : F) (x y : Fin n → F) :
    ggUForm σ (c • x) y = σ c * ggUForm σ x y := by
  simp only [ggUForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem ggUForm_smul_right (c : F) (x y : Fin n → F) :
    ggUForm σ x (c • y) = c * ggUForm σ x y := by
  simp only [ggUForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem ggUForm_zero_left (y : Fin n → F) : ggUForm σ 0 y = 0 := by
  simp [ggUForm]

theorem ggUForm_zero_right (x : Fin n → F) : ggUForm σ x 0 = 0 := by
  simp [ggUForm]

theorem ggUForm_sub_left (x x' y : Fin n → F) :
    ggUForm σ (x - x') y = ggUForm σ x y - ggUForm σ x' y := by
  simp only [ggUForm, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem ggUForm_sub_right (x y y' : Fin n → F) :
    ggUForm σ x (y - y') = ggUForm σ x y - ggUForm σ x y' := by
  simp only [ggUForm, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem ggUForm_sum_smul_left {ι : Type*} (s : Finset ι) (c : ι → F) (b : ι → Fin n → F)
    (y : Fin n → F) :
    ggUForm σ (∑ i ∈ s, c i • b i) y = ∑ i ∈ s, σ (c i) * ggUForm σ (b i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ggUForm_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ggUForm_add_left, ggUForm_smul_left, ih]

theorem ggUForm_sum_smul_right {ι : Type*} (s : Finset ι) (c : ι → F) (b : ι → Fin n → F)
    (x : Fin n → F) :
    ggUForm σ x (∑ i ∈ s, c i • b i) = ∑ i ∈ s, c i * ggUForm σ x (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ggUForm_zero_right]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ggUForm_add_right, ggUForm_smul_right, ih]

@[expose] def ggUFormL (x : Fin n → F) : (Fin n → F) →ₗ[F] F where
  toFun := ggUForm σ x
  map_add' := ggUForm_add_right σ x
  map_smul' c y := by rw [ggUForm_smul_right, smul_eq_mul, RingHom.id_apply]

theorem ggUFormL_apply (x y : Fin n → F) : ggUFormL σ x y = ggUForm σ x y := rfl

variable {σ}

theorem ggUForm_conj (hσ : ∀ c, σ (σ c) = c) (x y : Fin n → F) :
    ggUForm σ y x = σ (ggUForm σ x y) := by
  rw [ggUForm, ggUForm, map_sum]
  refine (Fintype.sum_equiv Fin.revPerm _ _ fun t => ?_).symm
  simp only [map_mul, hσ, Fin.revPerm_apply, Fin.rev_rev]
  ring

theorem ggUForm_single_right (x : Fin n → F) (i : Fin n) :
    ggUForm σ x (Pi.single i 1) = σ (x (Fin.rev i)) := by
  rw [ggUForm, Finset.sum_eq_single (Fin.rev i)]
  · rw [Fin.rev_rev, Pi.single_eq_same, mul_one]
  · intro t _ ht
    rw [Pi.single_eq_of_ne, mul_zero]
    intro h
    exact ht (by rw [← h, Fin.rev_rev])
  · simp

theorem eq_zero_of_ggUForm {x : Fin n → F} (hx : ∀ y, ggUForm σ x y = 0) : x = 0 := by
  funext i
  have h := hx (Pi.single (Fin.rev i) 1)
  rw [ggUForm_single_right, Fin.rev_rev, map_eq_zero_iff _ σ.injective] at h
  exact h

theorem eq_zero_of_ggUForm_right (hσ : ∀ c, σ (σ c) = c) {y : Fin n → F}
    (hy : ∀ x, ggUForm σ x y = 0) : y = 0 :=
  eq_zero_of_ggUForm fun x => by rw [ggUForm_conj hσ, hy, map_zero]

theorem conjTr_mul_antidiag_mul_apply_eq_ggUForm (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (conjTr σ A * antidiag n * A : Matrix (Fin n) (Fin n) F) i j =
      ggUForm σ (fun t => A t i) (fun t => A t j) := by
  rw [ggUForm_def]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [conjTr, transpose_apply, map_apply, antidiag, of_apply, mul_ite, ite_mul, mul_one,
    mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem mulVec_eq_sum_smul_col (A : Matrix (Fin n) (Fin n) F) (x : Fin n → F) :
    A *ᵥ x = ∑ c, x c • (fun t => A t c) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem ggUForm_mulVec {A : Matrix (Fin n) (Fin n) F}
    (hA : conjTr σ A * antidiag n * A = antidiag n) (x y : Fin n → F) :
    ggUForm σ (A *ᵥ x) (A *ᵥ y) = ggUForm σ x y := by
  rw [mulVec_eq_sum_smul_col A x, mulVec_eq_sum_smul_col A y, ggUForm_sum_smul_left]
  simp only [ggUForm_sum_smul_right, ← conjTr_mul_antidiag_mul_apply_eq_ggUForm, hA]
  rw [ggUForm_def]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [antidiag, of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem ggUForm_mulVec_left_eq {U : Matrix (Fin n) (Fin n) F}
    (hU : conjTr σ U * antidiag n * U = antidiag n) (hU2 : U * U = 1) (x y : Fin n → F) :
    ggUForm σ (U *ᵥ x) y = ggUForm σ x (U *ᵥ y) := by
  have hy : y = U *ᵥ (U *ᵥ y) := by rw [Matrix.mulVec_mulVec, hU2, Matrix.one_mulVec]
  conv_lhs => rw [hy]
  exact ggUForm_mulVec hU x (U *ᵥ y)

theorem ggUForm_sub_one_mulVec {U : Matrix (Fin n) (Fin n) F}
    (hU : conjTr σ U * antidiag n * U = antidiag n) (hU2 : U * U = 1) (x y : Fin n → F) :
    ggUForm σ ((U - 1) *ᵥ x) y = ggUForm σ x ((U - 1) *ᵥ y) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    ggUForm_sub_left, ggUForm_sub_right, ggUForm_mulVec_left_eq hU hU2]

end Form

end CFSG.StandardType
