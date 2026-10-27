module

public import CFSG.Blueprint.Catalog
import CFSG.Blueprint.SourceClassicalTransportOrthogonal
import CFSG.ClassicalGroups.Orthogonal.MatrixIsometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1OrthT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)

variable {K : Type} [Field K]

private def uc22s2112r34q35_eS7 : Fin 7 ≃ (Fin 3 ⊕ Fin 3 ⊕ Unit) where
  toFun := ![Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inl 1, Sum.inr (Sum.inl 1),
    Sum.inl 2, Sum.inr (Sum.inr ()), Sum.inr (Sum.inl 2)]
  invFun := fun i => match i with
    | .inl 0 => 0
    | .inr (.inl 0) => 1
    | .inl 1 => 2
    | .inr (.inl 1) => 3
    | .inl 2 => 4
    | .inr (.inr ()) => 5
    | .inr (.inl 2) => 6
  left_inv := by decide
  right_inv := by decide

private def uc22s2112r34q35_eT7 : Fin 7 ≃ (Fin 4 ⊕ Fin 3) where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0, Sum.inr 1, Sum.inr 2]
  invFun := fun i => match i with
    | .inl 0 => 0
    | .inl 1 => 1
    | .inl 2 => 2
    | .inl 3 => 3
    | .inr 0 => 4
    | .inr 1 => 5
    | .inr 2 => 6
  left_inv := by decide
  right_inv := by decide

private def uc22s2112r34q35_eS8 : Fin 8 ≃ (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) where
  toFun := ![Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inl 1, Sum.inr (Sum.inl 1),
    Sum.inl 2, Sum.inr (Sum.inl 2), Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)]
  invFun := fun i => match i with
    | .inl 0 => 0
    | .inr (.inl 0) => 1
    | .inl 1 => 2
    | .inr (.inl 1) => 3
    | .inl 2 => 4
    | .inr (.inl 2) => 5
    | .inr (.inr 0) => 6
    | .inr (.inr 1) => 7
  left_inv := by decide
  right_inv := by decide

private def uc22s2112r34q35_eT8 : Fin 8 ≃ (Fin 4 ⊕ Fin 4) where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0, Sum.inr 1,
    Sum.inr 2, Sum.inr 3]
  invFun := fun i => match i with
    | .inl 0 => 0
    | .inl 1 => 1
    | .inl 2 => 2
    | .inl 3 => 3
    | .inr 0 => 4
    | .inr 1 => 5
    | .inr 2 => 6
    | .inr 3 => 7
  left_inv := by decide
  right_inv := by decide

private def uc22s2112r34q35_M75 (K : Type) [Field K] : Matrix (Fin 7) (Fin 7) K :=
  !![3, 3, 0, 0, 0, 0, 0;
     4, -4, 0, 0, 0, 0, 0;
     0, 0, 3, 3, 0, 0, 0;
     0, 0, 4, -4, 0, 0, 0;
     0, 0, 0, 0, 3, 0, 3;
     0, 0, 0, 0, 4, 0, -4;
     0, 0, 0, 0, 0, 1, 0]

private def uc22s2112r34q35_N75 (K : Type) [Field K] : Matrix (Fin 7) (Fin 7) K :=
  !![1, 2, 0, 0, 0, 0, 0;
     1, -2, 0, 0, 0, 0, 0;
     0, 0, 1, 2, 0, 0, 0;
     0, 0, 1, -2, 0, 0, 0;
     0, 0, 0, 0, 1, 2, 0;
     0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, -2, 0]

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_M75_mul_N75 [CharP K 5] :
    uc22s2112r34q35_M75 K * uc22s2112r34q35_N75 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22s2112r34q35_M75, uc22s2112r34q35_N75, Matrix.mul_apply,
      Fin.sum_univ_seven]
  all_goals reduce_mod_char!

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_N75_mul_M75 [CharP K 5] :
    uc22s2112r34q35_N75 K * uc22s2112r34q35_M75 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22s2112r34q35_M75, uc22s2112r34q35_N75, Matrix.mul_apply,
      Fin.sum_univ_seven]
  all_goals reduce_mod_char!

private noncomputable def uc22s2112r34q35_L75fin (K : Type) [Field K] [CharP K 5] :
    (Fin 7 → K) ≃ₗ[K] (Fin 7 → K) :=
  Matrix.toLinOfInv (Pi.basisFun K (Fin 7)) (Pi.basisFun K (Fin 7))
    uc22s2112r34q35_M75_mul_N75 uc22s2112r34q35_N75_mul_M75

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_form75fin (K : Type) [Field K] [CharP K 5]
    (w : Fin 7 → K) :
    (∑ i, (uc22s2112r34q35_L75fin K w) i ^ 2) =
      w 0 * w 1 + w 2 * w 3 + w 4 * w 6 + w 5 ^ 2 := by
  rw [uc22s2112r34q35_L75fin, Matrix.toLinOfInv_apply, Matrix.toLin_eq_toLin',
    Matrix.toLin'_apply]
  simp [uc22s2112r34q35_M75, Matrix.mulVec, dotProduct, Fin.sum_univ_seven]
  have h5 : (5 : K) = 0 := by reduce_mod_char!
  linear_combination (5 * w 0 ^ 2 - 3 * w 0 * w 1 + 5 * w 1 ^ 2 +
      5 * w 2 ^ 2 - 3 * w 2 * w 3 + 5 * w 3 ^ 2 +
      5 * w 4 ^ 2 - 3 * w 4 * w 6 + 5 * w 6 ^ 2) * h5

private def uc22s2112r34q35_M73 (K : Type) [Field K] : Matrix (Fin 7) (Fin 7) K :=
  !![ -1, -1, 0, 0, 0, 0, 0;
     0, 0, -1, -1, 0, 0, 0;
     -1, 1, -1, 1, 0, 0, 0;
     -1, 1, 1, -1, 0, 0, 0;
     0, 0, 0, 0, -1, 0, -1;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, -1, 0, 1]

private def uc22s2112r34q35_N73 (K : Type) [Field K] : Matrix (Fin 7) (Fin 7) K :=
  !![1, 0, -1, -1, 0, 0, 0;
     1, 0, 1, 1, 0, 0, 0;
     0, 1, -1, 1, 0, 0, 0;
     0, 1, 1, -1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 1, 0, -1]

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_M73_mul_N73 [CharP K 3] :
    uc22s2112r34q35_M73 K * uc22s2112r34q35_N73 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22s2112r34q35_M73, uc22s2112r34q35_N73, Matrix.mul_apply,
      Fin.sum_univ_seven]
  all_goals try ring_nf
  all_goals reduce_mod_char!

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_N73_mul_M73 [CharP K 3] :
    uc22s2112r34q35_N73 K * uc22s2112r34q35_M73 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22s2112r34q35_M73, uc22s2112r34q35_N73, Matrix.mul_apply,
      Fin.sum_univ_seven]
  all_goals try ring_nf
  all_goals reduce_mod_char!

private noncomputable def uc22s2112r34q35_L73fin (K : Type) [Field K] [CharP K 3] :
    (Fin 7 → K) ≃ₗ[K] (Fin 7 → K) :=
  Matrix.toLinOfInv (Pi.basisFun K (Fin 7)) (Pi.basisFun K (Fin 7))
    uc22s2112r34q35_M73_mul_N73 uc22s2112r34q35_N73_mul_M73

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_form73fin (K : Type) [Field K] [CharP K 3]
    (w : Fin 7 → K) :
    (∑ i : Fin 7, (uc22s2112r34q35_L73fin K w) i ^ 2) +
        (uc22s2112r34q35_L73fin K w) 6 ^ 2 =
      w 0 * w 1 + w 2 * w 3 + w 4 * w 6 + w 5 ^ 2 := by
  rw [uc22s2112r34q35_L73fin, Matrix.toLinOfInv_apply, Matrix.toLin_eq_toLin',
    Matrix.toLin'_apply]
  simp [uc22s2112r34q35_M73, Matrix.mulVec, dotProduct, Fin.sum_univ_seven]
  have h3 : (3 : K) = 0 := by reduce_mod_char!
  linear_combination (w 0 ^ 2 - w 0 * w 1 + w 1 ^ 2 + w 2 ^ 2 - w 2 * w 3 + w 3 ^ 2 +
      w 4 ^ 2 - w 4 * w 6 + w 6 ^ 2) * h3

private def uc22s2112r34q35_M85 (K : Type) [Field K] (b : K) :
    Matrix (Fin 8) (Fin 8) K :=
  !![3, 3, 0, 0, 0, 0, 0, 0;
     4, -4, 0, 0, 0, 0, 0, 0;
     0, 0, 3, 3, 0, 0, 0, 0;
     0, 0, 4, -4, 0, 0, 0, 0;
     0, 0, 0, 0, 3, 3, 0, 0;
     0, 0, 0, 0, 4, -4, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 3 * b;
     0, 0, 0, 0, 0, 0, 0, 1]

private def uc22s2112r34q35_N85 (K : Type) [Field K] (b : K) :
    Matrix (Fin 8) (Fin 8) K :=
  !![1, 2, 0, 0, 0, 0, 0, 0;
     1, -2, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 2, 0, 0, 0, 0;
     0, 0, 1, -2, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 2, 0, 0;
     0, 0, 0, 0, 1, -2, 0, 0;
     0, 0, 0, 0, 0, 0, 1, -3 * b;
     0, 0, 0, 0, 0, 0, 0, 1]

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_M85_mul_N85 [CharP K 5] (b : K) :
    uc22s2112r34q35_M85 K b * uc22s2112r34q35_N85 K b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22s2112r34q35_M85, uc22s2112r34q35_N85, Matrix.mul_apply,
      Fin.sum_univ_eight]
  all_goals ring_nf
  all_goals reduce_mod_char!

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_N85_mul_M85 [CharP K 5] (b : K) :
    uc22s2112r34q35_N85 K b * uc22s2112r34q35_M85 K b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22s2112r34q35_M85, uc22s2112r34q35_N85, Matrix.mul_apply,
      Fin.sum_univ_eight]
  all_goals ring_nf
  all_goals reduce_mod_char!

private noncomputable def uc22s2112r34q35_L85fin (K : Type) [Field K] [CharP K 5]
    (b : K) : (Fin 8 → K) ≃ₗ[K] (Fin 8 → K) :=
  Matrix.toLinOfInv (Pi.basisFun K (Fin 8)) (Pi.basisFun K (Fin 8))
    (uc22s2112r34q35_M85_mul_N85 b) (uc22s2112r34q35_N85_mul_M85 b)

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_form85fin (K : Type) [Field K] [CharP K 5] (b c : K)
    (w : Fin 8 → K) :
    (∑ i : Fin 8, (uc22s2112r34q35_L85fin K b w) i ^ 2) +
        (c + b ^ 2 - 1) * (uc22s2112r34q35_L85fin K b w) 7 ^ 2 =
      w 0 * w 1 + w 2 * w 3 + w 4 * w 5 + w 6 ^ 2 + b * w 6 * w 7 + c * w 7 ^ 2 := by
  rw [uc22s2112r34q35_L85fin, Matrix.toLinOfInv_apply, Matrix.toLin_eq_toLin',
    Matrix.toLin'_apply]
  simp [uc22s2112r34q35_M85, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  have h5 : (5 : K) = 0 := by reduce_mod_char!
  linear_combination (5 * w 0 ^ 2 - 3 * w 0 * w 1 + 5 * w 1 ^ 2 +
      5 * w 2 ^ 2 - 3 * w 2 * w 3 + 5 * w 3 ^ 2 +
      5 * w 4 ^ 2 - 3 * w 4 * w 5 + 5 * w 5 ^ 2 +
      b * w 6 * w 7 + 2 * b ^ 2 * w 7 ^ 2) * h5

private def uc22s2112r34q35_M83 (K : Type) [Field K] (b : K) :
    Matrix (Fin 8) (Fin 8) K :=
  !![ -1, -1, 0, 0, 0, 0, 0, 0;
     0, 0, -1, -1, 0, 0, 0, 0;
     -1, 1, -1, 1, 0, 0, 0, 0;
     -1, 1, 1, -1, 0, 0, 0, 0;
     0, 0, 0, 0, -1, -1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, -b;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, -1, 1, 0, 0]

private def uc22s2112r34q35_N83 (K : Type) [Field K] (b : K) :
    Matrix (Fin 8) (Fin 8) K :=
  !![1, 0, -1, -1, 0, 0, 0, 0;
     1, 0, 1, 1, 0, 0, 0, 0;
     0, 1, -1, 1, 0, 0, 0, 0;
     0, 1, 1, -1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 1;
     0, 0, 0, 0, 1, 0, 0, -1;
     0, 0, 0, 0, 0, 1, b, 0;
     0, 0, 0, 0, 0, 0, 1, 0]

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_M83_mul_N83 [CharP K 3] (b : K) :
    uc22s2112r34q35_M83 K b * uc22s2112r34q35_N83 K b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22s2112r34q35_M83, uc22s2112r34q35_N83, Matrix.mul_apply,
      Fin.sum_univ_eight]
  all_goals try ring_nf
  all_goals reduce_mod_char!

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_N83_mul_M83 [CharP K 3] (b : K) :
    uc22s2112r34q35_N83 K b * uc22s2112r34q35_M83 K b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uc22s2112r34q35_M83, uc22s2112r34q35_N83, Matrix.mul_apply,
      Fin.sum_univ_eight]
  all_goals try ring_nf
  all_goals reduce_mod_char!

private noncomputable def uc22s2112r34q35_L83fin (K : Type) [Field K] [CharP K 3]
    (b : K) : (Fin 8 → K) ≃ₗ[K] (Fin 8 → K) :=
  Matrix.toLinOfInv (Pi.basisFun K (Fin 8)) (Pi.basisFun K (Fin 8))
    (uc22s2112r34q35_M83_mul_N83 b) (uc22s2112r34q35_N83_mul_M83 b)

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_form83fin (K : Type) [Field K] [CharP K 3] (b c : K)
    (hc : c = 1 + b ^ 2) (w : Fin 8 → K) :
    (∑ i : Fin 8, (uc22s2112r34q35_L83fin K b w) i ^ 2) +
        (uc22s2112r34q35_L83fin K b w) 7 ^ 2 =
      w 0 * w 1 + w 2 * w 3 + w 4 * w 5 + w 6 ^ 2 + b * w 6 * w 7 + c * w 7 ^ 2 := by
  rw [hc, uc22s2112r34q35_L83fin, Matrix.toLinOfInv_apply, Matrix.toLin_eq_toLin',
    Matrix.toLin'_apply]
  simp [uc22s2112r34q35_M83, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  have h3 : (3 : K) = 0 := by reduce_mod_char!
  linear_combination (w 0 ^ 2 - w 0 * w 1 + w 1 ^ 2 + w 2 ^ 2 - w 2 * w 3 + w 3 ^ 2 +
      w 4 ^ 2 - w 4 * w 5 + w 5 ^ 2 - b * w 6 * w 7) * h3

private noncomputable def uc22s2112r34q35_L75 (K : Type) [Field K] [CharP K 5] :
    ((Fin 3 ⊕ Fin 3 ⊕ Unit) → K) ≃ₗ[K] ((Fin 4 ⊕ Fin 3) → K) :=
  (LinearEquiv.funCongrLeft K K uc22s2112r34q35_eS7).trans
    ((uc22s2112r34q35_L75fin K).trans
      (LinearEquiv.funCongrLeft K K uc22s2112r34q35_eT7).symm)

private noncomputable def uc22s2112r34q35_L73 (K : Type) [Field K] [CharP K 3] :
    ((Fin 3 ⊕ Fin 3 ⊕ Unit) → K) ≃ₗ[K] ((Fin 4 ⊕ Fin 3) → K) :=
  (LinearEquiv.funCongrLeft K K uc22s2112r34q35_eS7).trans
    ((uc22s2112r34q35_L73fin K).trans
      (LinearEquiv.funCongrLeft K K uc22s2112r34q35_eT7).symm)

private noncomputable def uc22s2112r34q35_L85 (K : Type) [Field K] [CharP K 5] (b : K) :
    ((Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) → K) ≃ₗ[K] ((Fin 4 ⊕ Fin 4) → K) :=
  (LinearEquiv.funCongrLeft K K uc22s2112r34q35_eS8).trans
    ((uc22s2112r34q35_L85fin K b).trans
      (LinearEquiv.funCongrLeft K K uc22s2112r34q35_eT8).symm)

private noncomputable def uc22s2112r34q35_L83 (K : Type) [Field K] [CharP K 3] (b : K) :
    ((Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) → K) ≃ₗ[K] ((Fin 4 ⊕ Fin 4) → K) :=
  (LinearEquiv.funCongrLeft K K uc22s2112r34q35_eS8).trans
    ((uc22s2112r34q35_L83fin K b).trans
      (LinearEquiv.funCongrLeft K K uc22s2112r34q35_eT8).symm)

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_form75 (K : Type) [Field K] [CharP K 5]
    (v : (Fin 3 ⊕ Fin 3 ⊕ Unit) → K) :
    uc22s2112r34q35_Q7 (1 : K) (uc22s2112r34q35_L75 K v) = StatedQuadOdd 3 K v := by
  have hf : (LinearMap.funLeft K K ⇑uc22s2112r34q35_eS7) v =
      v ∘ uc22s2112r34q35_eS7 := by
    funext j
    simp [LinearMap.funLeft_apply]
  have hg : (LinearMap.funLeft K K ⇑uc22s2112r34q35_eT7.symm)
      (uc22s2112r34q35_L75fin K (v ∘ uc22s2112r34q35_eS7)) =
      (uc22s2112r34q35_L75fin K (v ∘ uc22s2112r34q35_eS7)) ∘
        uc22s2112r34q35_eT7.symm := by
    funext i
    simp [LinearMap.funLeft_apply]
  have hL : uc22s2112r34q35_L75 K v =
      (uc22s2112r34q35_L75fin K (v ∘ uc22s2112r34q35_eS7)) ∘
        uc22s2112r34q35_eT7.symm := by
    simp only [uc22s2112r34q35_L75, LinearEquiv.trans_apply,
      LinearEquiv.funCongrLeft_apply]
    rw [hf, LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, hg]
  rw [hL]
  have hQ : uc22s2112r34q35_Q7 (1 : K)
      ((uc22s2112r34q35_L75fin K (v ∘ uc22s2112r34q35_eS7)) ∘
        uc22s2112r34q35_eT7.symm) =
      ∑ i, (uc22s2112r34q35_L75fin K (v ∘ uc22s2112r34q35_eS7)) i ^ 2 := by
    simp [uc22s2112r34q35_Q7, uc22s2112r34q35_eT7, Fin.sum_univ_four,
      Fin.sum_univ_seven]
  rw [hQ, uc22s2112r34q35_form75fin]
  simp [StatedQuadOdd, uc22s2112r34q35_eS7, Fin.sum_univ_three]

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_form73 (K : Type) [Field K] [CharP K 3]
    (v : (Fin 3 ⊕ Fin 3 ⊕ Unit) → K) :
    uc22s2112r34q35_Q7 (2 : K) (uc22s2112r34q35_L73 K v) = StatedQuadOdd 3 K v := by
  have hf : (LinearMap.funLeft K K ⇑uc22s2112r34q35_eS7) v =
      v ∘ uc22s2112r34q35_eS7 := by
    funext j
    simp [LinearMap.funLeft_apply]
  have hg : (LinearMap.funLeft K K ⇑uc22s2112r34q35_eT7.symm)
      (uc22s2112r34q35_L73fin K (v ∘ uc22s2112r34q35_eS7)) =
      (uc22s2112r34q35_L73fin K (v ∘ uc22s2112r34q35_eS7)) ∘
        uc22s2112r34q35_eT7.symm := by
    funext i
    simp [LinearMap.funLeft_apply]
  have hL : uc22s2112r34q35_L73 K v =
      (uc22s2112r34q35_L73fin K (v ∘ uc22s2112r34q35_eS7)) ∘
        uc22s2112r34q35_eT7.symm := by
    simp only [uc22s2112r34q35_L73, LinearEquiv.trans_apply,
      LinearEquiv.funCongrLeft_apply]
    rw [hf, LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, hg]
  rw [hL]
  have hQ : uc22s2112r34q35_Q7 (2 : K)
      ((uc22s2112r34q35_L73fin K (v ∘ uc22s2112r34q35_eS7)) ∘
        uc22s2112r34q35_eT7.symm) =
      (∑ i : Fin 7, (uc22s2112r34q35_L73fin K (v ∘ uc22s2112r34q35_eS7)) i ^ 2) +
        (uc22s2112r34q35_L73fin K (v ∘ uc22s2112r34q35_eS7)) 6 ^ 2 := by
    simp [uc22s2112r34q35_Q7, uc22s2112r34q35_eT7, Fin.sum_univ_four,
      Fin.sum_univ_seven]
    ring
  rw [hQ, uc22s2112r34q35_form73fin]
  simp [StatedQuadOdd, uc22s2112r34q35_eS7, Fin.sum_univ_three]

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_form85 (K : Type) [Field K] [CharP K 5] (b c : K)
    (v : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) → K) :
    uc22s2112r34q35_Q8 (c + b ^ 2) (uc22s2112r34q35_L85 K b v) =
      StatedQuadMinus 4 K b c v := by
  have hf : (LinearMap.funLeft K K ⇑uc22s2112r34q35_eS8) v =
      v ∘ uc22s2112r34q35_eS8 := by
    funext j
    simp [LinearMap.funLeft_apply]
  have hg : (LinearMap.funLeft K K ⇑uc22s2112r34q35_eT8.symm)
      (uc22s2112r34q35_L85fin K b (v ∘ uc22s2112r34q35_eS8)) =
      (uc22s2112r34q35_L85fin K b (v ∘ uc22s2112r34q35_eS8)) ∘
        uc22s2112r34q35_eT8.symm := by
    funext i
    simp [LinearMap.funLeft_apply]
  have hL : uc22s2112r34q35_L85 K b v =
      (uc22s2112r34q35_L85fin K b (v ∘ uc22s2112r34q35_eS8)) ∘
        uc22s2112r34q35_eT8.symm := by
    simp only [uc22s2112r34q35_L85, LinearEquiv.trans_apply,
      LinearEquiv.funCongrLeft_apply]
    rw [hf, LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, hg]
  rw [hL]
  have hQ : uc22s2112r34q35_Q8 (c + b ^ 2)
      ((uc22s2112r34q35_L85fin K b (v ∘ uc22s2112r34q35_eS8)) ∘
        uc22s2112r34q35_eT8.symm) =
      (∑ i : Fin 8, (uc22s2112r34q35_L85fin K b (v ∘ uc22s2112r34q35_eS8)) i ^ 2) +
        (c + b ^ 2 - 1) *
          (uc22s2112r34q35_L85fin K b (v ∘ uc22s2112r34q35_eS8)) 7 ^ 2 := by
    simp [uc22s2112r34q35_Q8, uc22s2112r34q35_eT8, Fin.sum_univ_four,
      Fin.sum_univ_eight]
    ring
  rw [hQ, uc22s2112r34q35_form85fin]
  simp [StatedQuadMinus, uc22s2112r34q35_eS8, Fin.sum_univ_three]

set_option maxHeartbeats 400000 in
private lemma uc22s2112r34q35_form83 (K : Type) [Field K] [CharP K 3] (b c : K)
    (hc : c = 1 + b ^ 2) (v : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) → K) :
    uc22s2112r34q35_Q8 (2 : K) (uc22s2112r34q35_L83 K b v) =
      StatedQuadMinus 4 K b c v := by
  have hf : (LinearMap.funLeft K K ⇑uc22s2112r34q35_eS8) v =
      v ∘ uc22s2112r34q35_eS8 := by
    funext j
    simp [LinearMap.funLeft_apply]
  have hg : (LinearMap.funLeft K K ⇑uc22s2112r34q35_eT8.symm)
      (uc22s2112r34q35_L83fin K b (v ∘ uc22s2112r34q35_eS8)) =
      (uc22s2112r34q35_L83fin K b (v ∘ uc22s2112r34q35_eS8)) ∘
        uc22s2112r34q35_eT8.symm := by
    funext i
    simp [LinearMap.funLeft_apply]
  have hL : uc22s2112r34q35_L83 K b v =
      (uc22s2112r34q35_L83fin K b (v ∘ uc22s2112r34q35_eS8)) ∘
        uc22s2112r34q35_eT8.symm := by
    simp only [uc22s2112r34q35_L83, LinearEquiv.trans_apply,
      LinearEquiv.funCongrLeft_apply]
    rw [hf, LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, hg]
  rw [hL]
  have hQ : uc22s2112r34q35_Q8 (2 : K)
      ((uc22s2112r34q35_L83fin K b (v ∘ uc22s2112r34q35_eS8)) ∘
        uc22s2112r34q35_eT8.symm) =
      (∑ i : Fin 8, (uc22s2112r34q35_L83fin K b (v ∘ uc22s2112r34q35_eS8)) i ^ 2) +
        (uc22s2112r34q35_L83fin K b (v ∘ uc22s2112r34q35_eS8)) 7 ^ 2 := by
    simp [uc22s2112r34q35_Q8, uc22s2112r34q35_eT8, Fin.sum_univ_four,
      Fin.sum_univ_eight]
    ring
  rw [hQ, uc22s2112r34q35_form83fin K b c hc]
  simp [StatedQuadMinus, uc22s2112r34q35_eS8, Fin.sum_univ_three]

private lemma uc22s2112r34q35_matrixOrthogonal_eq_orthogonalGroup {ι : Type} [Fintype ι]
    [DecidableEq ι] (Q : (ι → K) → K) :
    CFSG.Blueprint.EvenSource.matrixOrthogonal Q = CFSG.PGLModel.orthogonalGroup Q := by
  ext A
  exact (CFSG.PGLModel.mem_orthogonalGroup_iff).symm

private lemma uc22s2112r34q35_card_orthogonalGroup_eq_of_linearEquiv
    {ιs ιt : Type} [Fintype ιs] [DecidableEq ιs] [Fintype ιt] [DecidableEq ιt]
    {Q_st : (ιs → K) → K} {Q_c : (ιt → K) → K}
    (L : (ιs → K) ≃ₗ[K] (ιt → K)) (hQ : ∀ x, Q_st x = Q_c (L x)) :
    Nat.card (CFSG.PGLModel.orthogonalGroup Q_c) =
      Nat.card (CFSG.PGLModel.orthogonalGroup Q_st) := by
  let bs : Module.Basis ιt K (ιs → K) := Module.Basis.ofEquivFun L
  have hbs : bs.equivFun = L := Module.Basis.equivFun_ofEquivFun L
  have hQb : ∀ x, Q_st x = Q_c (bs.equivFun x) := fun x => by
    rw [hbs]
    exact hQ x
  have hmap1 : (CFSG.Blueprint.EvenSource.sourceOrthogonal Q_st).map
      (CFSG.Blueprint.EvenSource.sourceGLEquiv bs).toMonoidHom =
      CFSG.Blueprint.EvenSource.matrixOrthogonal Q_c :=
    CFSG.Blueprint.EvenSource.map_sourceOrthogonal bs hQb
  have hmap2 : (CFSG.Blueprint.EvenSource.sourceOrthogonal Q_st).map
      (CFSG.Blueprint.EvenSource.sourceGLEquiv (Pi.basisFun K ιs)).toMonoidHom =
      CFSG.Blueprint.EvenSource.matrixOrthogonal Q_st :=
    CFSG.Blueprint.EvenSource.map_sourceOrthogonal (Pi.basisFun K ιs)
      (Q := Q_st) (Q₀ := Q_st) (fun x => by simp)
  have h1 : Nat.card (CFSG.Blueprint.EvenSource.matrixOrthogonal Q_c) =
      Nat.card (CFSG.Blueprint.EvenSource.sourceOrthogonal Q_st) := by
    rw [← hmap1]
    exact Subgroup.card_map_of_injective
      (CFSG.Blueprint.EvenSource.sourceGLEquiv bs).injective
  have h2 : Nat.card (CFSG.Blueprint.EvenSource.matrixOrthogonal Q_st) =
      Nat.card (CFSG.Blueprint.EvenSource.sourceOrthogonal Q_st) := by
    rw [← hmap2]
    exact Subgroup.card_map_of_injective
      (CFSG.Blueprint.EvenSource.sourceGLEquiv (Pi.basisFun K ιs)).injective
  rw [← uc22s2112r34q35_matrixOrthogonal_eq_orthogonalGroup Q_c,
    ← uc22s2112r34q35_matrixOrthogonal_eq_orthogonalGroup Q_st, h1, h2]

private lemma uc22s2112r34q35_card_orthogonalGroup_eq_quad
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm K (ι → K)}
    {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    Nat.card (CFSG.PGLModel.orthogonalGroup Q₀) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hcore : CFSG.MatrixModel.isometryCore Q₀ =
      CFSG.Blueprint.EvenSource.matrixOrthogonal Q₀ :=
    Subgroup.closure_eq (CFSG.Blueprint.EvenSource.matrixOrthogonal Q₀)
  have hmap : (TauCeti.QuadraticMap.orthogonalGroup Q).map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm.toMonoidHom =
      CFSG.MatrixModel.isometryCore Q₀ :=
    (Subgroup.comap_equiv_eq_map_symm (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K)
      _).symm.trans (CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap hQ).symm
  have hcardO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      Nat.card (CFSG.Blueprint.EvenSource.matrixOrthogonal Q₀) := by
    rw [← hcore, ← hmap]
    exact (Subgroup.card_map_of_injective
      (f := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm.toMonoidHom)
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm.injective).symm
  rw [← uc22s2112r34q35_matrixOrthogonal_eq_orthogonalGroup Q₀]
  exact hcardO.symm

private lemma uc22s2112r34q35_factorization_two {N m k : ℕ} (hN : N = 2 ^ k * m)
    (hm : ¬ 2 ∣ m) : N.factorization 2 = k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [hN, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

private lemma uc22s2112r34q35_card_quadOdd_three_five [Finite K] (h2 : (2 : K) ≠ 0)
    (hq : Nat.card K = 5) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadOdd 3 K)) = 914004000000000 := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadOdd (K := K) h2 3
  rw [hq] at h
  have hR : (2 : ℤ) * ((5 : ℕ) : ℤ) ^ (3 ^ 2) *
      ∏ i ∈ Finset.Icc 1 3, ((((5 : ℕ) : ℤ) ^ 2) ^ i - 1) = 914004000000000 := by
    norm_num [Finset.prod_Icc_succ_top]
  rw [hR] at h
  exact_mod_cast h

private lemma uc22s2112r34q35_card_quadOdd_three_three [Finite K] (h2 : (2 : K) ≠ 0)
    (hq : Nat.card K = 3) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadOdd 3 K)) = 18341406720 := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadOdd (K := K) h2 3
  rw [hq] at h
  have hR : (2 : ℤ) * ((3 : ℕ) : ℤ) ^ (3 ^ 2) *
      ∏ i ∈ Finset.Icc 1 3, ((((3 : ℕ) : ℤ) ^ 2) ^ i - 1) = 18341406720 := by
    norm_num [Finset.prod_Icc_succ_top]
  rw [hR] at h
  exact_mod_cast h

private lemma uc22s2112r34q35_card_quadMinus_four_five [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hq : Nat.card K = 5) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) = 71520813000000000000 := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus
    (K := K) hirr 3
  rw [hq] at h
  have hR : (2 : ℤ) * ((5 : ℕ) : ℤ) ^ (3 * (3 + 1)) *
      ((((5 : ℕ) : ℤ)) ^ (3 + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 3, ((((5 : ℕ) : ℤ) ^ 2) ^ i - 1) = 71520813000000000000 := by
    norm_num [Finset.prod_Icc_succ_top]
  rw [hR] at h
  exact_mod_cast h

private lemma uc22s2112r34q35_card_quadMinus_four_three [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hq : Nat.card K = 3) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) = 40607874478080 := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus
    (K := K) hirr 3
  rw [hq] at h
  have hR : (2 : ℤ) * ((3 : ℕ) : ℤ) ^ (3 * (3 + 1)) *
      ((((3 : ℕ) : ℤ)) ^ (3 + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 3, ((((3 : ℕ) : ℤ) ^ 2) ^ i - 1) = 40607874478080 := by
    norm_num [Finset.prod_Icc_succ_top]
  rw [hR] at h
  exact_mod_cast h

private lemma uc22s2112r34q35_three_eq_zero {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 3) : (3 : F) = 0 := by
  have h := FiniteField.cast_card_eq_zero (K := F)
  rwa [hF] at h

private lemma uc22s2112r34q35_eq_zero_or_eq_one_or_eq_neg_one {F : Type*} [Field F]
    [Fintype F] (hF : Fintype.card F = 3) (x : F) : x = 0 ∨ x = 1 ∨ x = -1 := by
  classical
  have h3 : (3 : F) = 0 := uc22s2112r34q35_three_eq_zero hF
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

private lemma uc22s2112r34q35_coeff_eq_one_add_sq {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 3) {b c : F} (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    c = 1 + b ^ 2 := by
  have h3 : (3 : F) = 0 := uc22s2112r34q35_three_eq_zero hF
  rcases uc22s2112r34q35_eq_zero_or_eq_one_or_eq_neg_one hF b with rfl | rfl | rfl <;>
    rcases uc22s2112r34q35_eq_zero_or_eq_one_or_eq_neg_one hF c with rfl | rfl | rfl
  · exfalso; exact hbc 0 (by norm_num)
  · norm_num
  · exfalso; exact hbc 1 (by norm_num)
  · exfalso; exact hbc 0 (by norm_num)
  · exfalso; exact hbc 1 (by linear_combination h3)
  · linear_combination -h3
  · exfalso; exact hbc 0 (by norm_num)
  · exfalso; exact hbc (-1) (by linear_combination h3)
  · linear_combination -h3

theorem uc22s2112r34q35_exists_model_Q7 {X : Type} [Group X] {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hX : LieModel X .POmegaOdd 3 p 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (e : K), (Nat.card K = 3 ∨ Nat.card K = 5) ∧
      e ≠ 0 ∧
      (Nat.card (CFSG.PGLModel.orthogonalGroup (uc22s2112r34q35_Q7 e))).factorization 2 = 11 ∧
      Nonempty (X ≃* StatedProj (StatedOmega (uc22s2112r34q35_Q7 e))) := by
  obtain ⟨-, K, hField, hFinite, hK, ⟨eX⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hField
  let : Finite K := hFinite
  have : Fintype K := Fintype.ofFinite K
  have hKp : Nat.card K = p := by simpa using hK
  rcases hp with rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : CharP K 3 := charP_of_card_eq_prime_pow (f := 1) (by
      rw [← Nat.card_eq_fintype_card]
      exact hK)
    have hK3 : Nat.card K = 3 := hKp
    have h2 : (2 : K) ≠ 0 := by
      intro hzero
      have hdvd := (CharP.cast_eq_zero_iff K 3 2).mp hzero
      omega
    have hmodel : Nonempty
        (X ≃* StatedProj (StatedOmega (uc22s2112r34q35_Q7 (2 : K)))) := by
      obtain ⟨e1⟩ := CFSG.Blueprint.EvenSource.nonempty_statedProj_statedOmega_equiv
        (StatedQuadOdd 3 K)
      let L := uc22s2112r34q35_L73 K
      let bs : Module.Basis (Fin 4 ⊕ Fin 3) K
          ((Fin 3 ⊕ Fin 3 ⊕ Unit) → K) := Module.Basis.ofEquivFun L
      have hbs : bs.equivFun = L := Module.Basis.equivFun_ofEquivFun L
      have hQb : ∀ x, StatedQuadOdd 3 K x =
          uc22s2112r34q35_Q7 (2 : K) (bs.equivFun x) := fun x => by
        rw [hbs]
        exact (uc22s2112r34q35_form73 K x).symm
      exact ⟨eX.trans (e1.trans (CFSG.Blueprint.EvenSource.quotientInfCongr
        (CFSG.Blueprint.EvenSource.sourceGLEquiv bs)
        (CFSG.Blueprint.EvenSource.map_sourceOmega bs hQb)
        (CFSG.Blueprint.EvenSource.map_sourceScalars_sourceGLEquiv bs)))⟩
    have hcard : (Nat.card (CFSG.PGLModel.orthogonalGroup
        (uc22s2112r34q35_Q7 (2 : K)))).factorization 2 = 11 := by
      have hcard1 := uc22s2112r34q35_card_orthogonalGroup_eq_of_linearEquiv
        (L := uc22s2112r34q35_L73 K) (Q_st := StatedQuadOdd 3 K)
        (Q_c := uc22s2112r34q35_Q7 (2 : K))
        (fun x => (uc22s2112r34q35_form73 K x).symm)
      have hcard2 := uc22s2112r34q35_card_orthogonalGroup_eq_quad
        (Q := CFSG.LieType.Universal.Spin.quadOdd 3 K)
        (Q₀ := StatedQuadOdd 3 K) (CFSG.LieType.Universal.Spin.coe_quadOdd 3 K)
      have hval := uc22s2112r34q35_card_quadOdd_three_three (K := K) h2 hK3
      rw [hcard1, hcard2, hval]
      exact uc22s2112r34q35_factorization_two (N := 18341406720) (m := 8955765)
        (k := 11) (by norm_num) (by norm_num)
    exact ⟨K, hField, hFinite, (2 : K), Or.inl hK3, h2, hcard, hmodel⟩
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : CharP K 5 := charP_of_card_eq_prime_pow (f := 1) (by
      rw [← Nat.card_eq_fintype_card]
      exact hK)
    have hK5 : Nat.card K = 5 := hKp
    have h2 : (2 : K) ≠ 0 := by
      intro hzero
      have hdvd := (CharP.cast_eq_zero_iff K 5 2).mp hzero
      omega
    have hmodel : Nonempty
        (X ≃* StatedProj (StatedOmega (uc22s2112r34q35_Q7 (1 : K)))) := by
      obtain ⟨e1⟩ := CFSG.Blueprint.EvenSource.nonempty_statedProj_statedOmega_equiv
        (StatedQuadOdd 3 K)
      let L := uc22s2112r34q35_L75 K
      let bs : Module.Basis (Fin 4 ⊕ Fin 3) K
          ((Fin 3 ⊕ Fin 3 ⊕ Unit) → K) := Module.Basis.ofEquivFun L
      have hbs : bs.equivFun = L := Module.Basis.equivFun_ofEquivFun L
      have hQb : ∀ x, StatedQuadOdd 3 K x =
          uc22s2112r34q35_Q7 (1 : K) (bs.equivFun x) := fun x => by
        rw [hbs]
        exact (uc22s2112r34q35_form75 K x).symm
      exact ⟨eX.trans (e1.trans (CFSG.Blueprint.EvenSource.quotientInfCongr
        (CFSG.Blueprint.EvenSource.sourceGLEquiv bs)
        (CFSG.Blueprint.EvenSource.map_sourceOmega bs hQb)
        (CFSG.Blueprint.EvenSource.map_sourceScalars_sourceGLEquiv bs)))⟩
    have hcard : (Nat.card (CFSG.PGLModel.orthogonalGroup
        (uc22s2112r34q35_Q7 (1 : K)))).factorization 2 = 11 := by
      have hcard1 := uc22s2112r34q35_card_orthogonalGroup_eq_of_linearEquiv
        (L := uc22s2112r34q35_L75 K) (Q_st := StatedQuadOdd 3 K)
        (Q_c := uc22s2112r34q35_Q7 (1 : K))
        (fun x => (uc22s2112r34q35_form75 K x).symm)
      have hcard2 := uc22s2112r34q35_card_orthogonalGroup_eq_quad
        (Q := CFSG.LieType.Universal.Spin.quadOdd 3 K)
        (Q₀ := StatedQuadOdd 3 K) (CFSG.LieType.Universal.Spin.coe_quadOdd 3 K)
      have hval := uc22s2112r34q35_card_quadOdd_three_five (K := K) h2 hK5
      rw [hcard1, hcard2, hval]
      exact uc22s2112r34q35_factorization_two (N := 914004000000000) (m := 446291015625)
        (k := 11) (by norm_num) (by norm_num)
    exact ⟨K, hField, hFinite, (1 : K), Or.inr hK5, one_ne_zero, hcard, hmodel⟩

theorem uc22s2112r34q35_exists_model_Q8 {X : Type} [Group X] {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hX : LieModel X .POmegaMinus 4 p 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (e : K), (Nat.card K = 3 ∨ Nat.card K = 5) ∧
      e ≠ 0 ∧
      (Nat.card (CFSG.PGLModel.orthogonalGroup (uc22s2112r34q35_Q8 e))).factorization 2 = 12 ∧
      Nonempty (X ≃* StatedProj (StatedOmega (uc22s2112r34q35_Q8 e))) := by
  obtain ⟨-, K, hField, hFinite, hK, b, c, hirr, ⟨eX⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hField
  let : Finite K := hFinite
  have : Fintype K := Fintype.ofFinite K
  have hKp : Nat.card K = p := by simpa using hK
  rcases hp with rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : CharP K 3 := charP_of_card_eq_prime_pow (f := 1) (by
      rw [← Nat.card_eq_fintype_card]
      exact hK)
    have hK3 : Nat.card K = 3 := hKp
    have h2 : (2 : K) ≠ 0 := by
      intro hzero
      have hdvd := (CharP.cast_eq_zero_iff K 3 2).mp hzero
      omega
    have hF : Fintype.card K = 3 := by
      rw [← Nat.card_eq_fintype_card]
      exact hK3
    have hc : c = 1 + b ^ 2 := uc22s2112r34q35_coeff_eq_one_add_sq hF hirr
    have hmodel : Nonempty
        (X ≃* StatedProj (StatedOmega (uc22s2112r34q35_Q8 (2 : K)))) := by
      obtain ⟨e1⟩ := CFSG.Blueprint.EvenSource.nonempty_statedProj_statedOmega_equiv
        (StatedQuadMinus 4 K b c)
      let L := uc22s2112r34q35_L83 K b
      let bs : Module.Basis (Fin 4 ⊕ Fin 4) K
          ((Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) → K) := Module.Basis.ofEquivFun L
      have hbs : bs.equivFun = L := Module.Basis.equivFun_ofEquivFun L
      have hQb : ∀ x, StatedQuadMinus 4 K b c x =
          uc22s2112r34q35_Q8 (2 : K) (bs.equivFun x) := fun x => by
        rw [hbs]
        exact (uc22s2112r34q35_form83 K b c hc x).symm
      exact ⟨eX.trans (e1.trans (CFSG.Blueprint.EvenSource.quotientInfCongr
        (CFSG.Blueprint.EvenSource.sourceGLEquiv bs)
        (CFSG.Blueprint.EvenSource.map_sourceOmega bs hQb)
        (CFSG.Blueprint.EvenSource.map_sourceScalars_sourceGLEquiv bs)))⟩
    have hcard : (Nat.card (CFSG.PGLModel.orthogonalGroup
        (uc22s2112r34q35_Q8 (2 : K)))).factorization 2 = 12 := by
      have hcard1 := uc22s2112r34q35_card_orthogonalGroup_eq_of_linearEquiv
        (L := uc22s2112r34q35_L83 K b) (Q_st := StatedQuadMinus 4 K b c)
        (Q_c := uc22s2112r34q35_Q8 (2 : K))
        (fun x => (uc22s2112r34q35_form83 K b c hc x).symm)
      have hcard2 := uc22s2112r34q35_card_orthogonalGroup_eq_quad
        (Q := CFSG.LieType.Universal.Spin.quadMinus 4 K b c)
        (Q₀ := StatedQuadMinus 4 K b c)
        (CFSG.LieType.Universal.Spin.coe_quadMinus 4 K b c)
      have hval := uc22s2112r34q35_card_quadMinus_four_three (K := K) hirr hK3
      rw [hcard1, hcard2, hval]
      exact uc22s2112r34q35_factorization_two (N := 40607874478080) (m := 9914031855)
        (k := 12) (by norm_num) (by norm_num)
    exact ⟨K, hField, hFinite, (2 : K), Or.inl hK3, h2, hcard, hmodel⟩
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : CharP K 5 := charP_of_card_eq_prime_pow (f := 1) (by
      rw [← Nat.card_eq_fintype_card]
      exact hK)
    have hK5 : Nat.card K = 5 := hKp
    have h2 : (2 : K) ≠ 0 := by
      intro hzero
      have hdvd := (CharP.cast_eq_zero_iff K 5 2).mp hzero
      omega
    have he : c + b ^ 2 ≠ 0 := by
      intro hzero
      have hroot : (2 * b) ^ 2 + b * (2 * b) + c = 0 := by
        have h5 : (5 : K) = 0 := by reduce_mod_char!
        linear_combination hzero + b ^ 2 * h5
      exact hirr (2 * b) hroot
    have hmodel : Nonempty
        (X ≃* StatedProj (StatedOmega (uc22s2112r34q35_Q8 (c + b ^ 2)))) := by
      obtain ⟨e1⟩ := CFSG.Blueprint.EvenSource.nonempty_statedProj_statedOmega_equiv
        (StatedQuadMinus 4 K b c)
      let L := uc22s2112r34q35_L85 K b
      let bs : Module.Basis (Fin 4 ⊕ Fin 4) K
          ((Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) → K) := Module.Basis.ofEquivFun L
      have hbs : bs.equivFun = L := Module.Basis.equivFun_ofEquivFun L
      have hQb : ∀ x, StatedQuadMinus 4 K b c x =
          uc22s2112r34q35_Q8 (c + b ^ 2) (bs.equivFun x) := fun x => by
        rw [hbs]
        exact (uc22s2112r34q35_form85 K b c x).symm
      exact ⟨eX.trans (e1.trans (CFSG.Blueprint.EvenSource.quotientInfCongr
        (CFSG.Blueprint.EvenSource.sourceGLEquiv bs)
        (CFSG.Blueprint.EvenSource.map_sourceOmega bs hQb)
        (CFSG.Blueprint.EvenSource.map_sourceScalars_sourceGLEquiv bs)))⟩
    have hcard : (Nat.card (CFSG.PGLModel.orthogonalGroup
        (uc22s2112r34q35_Q8 (c + b ^ 2)))).factorization 2 = 12 := by
      have hcard1 := uc22s2112r34q35_card_orthogonalGroup_eq_of_linearEquiv
        (L := uc22s2112r34q35_L85 K b) (Q_st := StatedQuadMinus 4 K b c)
        (Q_c := uc22s2112r34q35_Q8 (c + b ^ 2))
        (fun x => (uc22s2112r34q35_form85 K b c x).symm)
      have hcard2 := uc22s2112r34q35_card_orthogonalGroup_eq_quad
        (Q := CFSG.LieType.Universal.Spin.quadMinus 4 K b c)
        (Q₀ := StatedQuadMinus 4 K b c)
        (CFSG.LieType.Universal.Spin.coe_quadMinus 4 K b c)
      have hval := uc22s2112r34q35_card_quadMinus_four_five (K := K) hirr hK5
      rw [hcard1, hcard2, hval]
      exact uc22s2112r34q35_factorization_two (N := 71520813000000000000)
        (m := 17461135986328125) (k := 12) (by norm_num) (by norm_num)
    exact ⟨K, hField, hFinite, c + b ^ 2, Or.inr hK5, he, hcard, hmodel⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
