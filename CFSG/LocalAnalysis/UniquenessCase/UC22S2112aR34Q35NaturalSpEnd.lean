module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalTrace
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalGL42Fix
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalSpEigen
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalSpSingular
import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix CFSG.Open

variable {K : Type} [Field K]

private def spJ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 0 1 (-1) 0

private lemma spJ_inl_inr (i j : Fin 2) :
    spJ (Sum.inl i) (Sum.inr j) = if i = j then (1 : K) else 0 := by
  simp [spJ, Matrix.fromBlocks_apply₁₂, Matrix.one_apply]

private lemma spJ_inl_zero_inr_zero : spJ (Sum.inl 0) (Sum.inr 0) = (1 : K) := by
  rw [spJ_inl_inr]
  simp

private lemma gl_neg_mul (a b : GL (Fin 2 ⊕ Fin 2) K) : -(a * b) = (-a) * b := by
  apply Units.ext
  rw [Units.val_neg, Units.val_mul, Units.val_mul, Units.val_neg, neg_mul]

private lemma gl_mul_neg (a b : GL (Fin 2 ⊕ Fin 2) K) : -(a * b) = a * (-b) := by
  apply Units.ext
  rw [Units.val_neg, Units.val_mul, Units.val_mul, Units.val_neg, mul_neg]

private lemma gl_neg_neg (a : GL (Fin 2 ⊕ Fin 2) K) : -(-a) = a := by
  apply Units.ext
  rw [Units.val_neg, Units.val_neg, neg_neg]

private lemma gl_neg_one_mul (a : GL (Fin 2 ⊕ Fin 2) K) :
    (-1 : GL (Fin 2 ⊕ Fin 2) K) * a = -a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul, Units.val_neg]

private lemma gl_neg_mul_neg_one (a : GL (Fin 2 ⊕ Fin 2) K) :
    a * (-1 : GL (Fin 2 ⊕ Fin 2) K) = -a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_neg, Units.val_one, mul_neg_one, Units.val_neg]

private lemma gl_conj_neg (T X : GL (Fin 2 ⊕ Fin 2) K) :
    T * (-X) * T⁻¹ = -(T * X * T⁻¹) := by
  rw [← gl_mul_neg T X, ← gl_neg_mul (T * X) T⁻¹]

private lemma gl_inv_conj_neg (T X : GL (Fin 2 ⊕ Fin 2) K) :
    T⁻¹ * (-X) * T = -(T⁻¹ * X * T) := by
  rw [← gl_mul_neg T⁻¹ X, ← gl_neg_mul (T⁻¹ * X) T]

private def Smat (S : ZMod 5 → GL (Fin 2 ⊕ Fin 2) K) (i : ZMod 5) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  (S i : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

private lemma smat_pair_sq (S : ZMod 5 → GL (Fin 2 ⊕ Fin 2) K)
    (hSsq : ∀ i, Smat S i * Smat S i = 1)
    (hSanti : ∀ i j, i ≠ j → Smat S i * Smat S j = -(Smat S j * Smat S i))
    {a b : ZMod 5} (hab : a ≠ b) :
    (((S a * S b : GL (Fin 2 ⊕ Fin 2) K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (((S a * S b : GL (Fin 2 ⊕ Fin 2) K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
  have hval : (((S a * S b : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Smat S a * Smat S b := rfl
  rw [hval]
  calc
    Smat S a * Smat S b * (Smat S a * Smat S b)
        = Smat S a * (Smat S b * Smat S a) * Smat S b := by noncomm_ring
    _ = Smat S a * (-(Smat S a * Smat S b)) * Smat S b := by rw [hSanti b a hab.symm]
    _ = -(Smat S a * (Smat S a * Smat S b) * Smat S b) := by rw [mul_neg, neg_mul]
    _ = -((Smat S a * Smat S a) * (Smat S b * Smat S b)) := by
        rw [show Smat S a * (Smat S a * Smat S b) * Smat S b =
          (Smat S a * Smat S a) * (Smat S b * Smat S b) by noncomm_ring]
    _ = -1 := by rw [hSsq a, hSsq b, mul_one]

private lemma smat_comm_pair (S : ZMod 5 → GL (Fin 2 ⊕ Fin 2) K)
    (hSanti : ∀ i j, i ≠ j → Smat S i * Smat S j = -(Smat S j * Smat S i))
    {a b c : ZMod 5} (hca : c ≠ a) (hcb : c ≠ b) :
    Smat S c * (Smat S a * Smat S b) = (Smat S a * Smat S b) * Smat S c := by
  calc
    Smat S c * (Smat S a * Smat S b) = (Smat S c * Smat S a) * Smat S b := by noncomm_ring
    _ = (-(Smat S a * Smat S c)) * Smat S b := by rw [hSanti c a hca]
    _ = -(Smat S a * Smat S c * Smat S b) := by rw [neg_mul]
    _ = -(Smat S a * (Smat S c * Smat S b)) := by rw [mul_assoc]
    _ = -(Smat S a * (-(Smat S b * Smat S c))) := by rw [hSanti c b hcb]
    _ = -(-(Smat S a * (Smat S b * Smat S c))) := by rw [mul_neg]
    _ = Smat S a * (Smat S b * Smat S c) := by rw [neg_neg]
    _ = (Smat S a * Smat S b) * Smat S c := by rw [mul_assoc]

private lemma smat_pair_mul_left (S : ZMod 5 → GL (Fin 2 ⊕ Fin 2) K)
    (hSsq : ∀ i, Smat S i * Smat S i = 1)
    (hSanti : ∀ i j, i ≠ j → Smat S i * Smat S j = -(Smat S j * Smat S i))
    {a b : ZMod 5} (hab : a ≠ b) :
    (Smat S a * Smat S b) * Smat S a = -Smat S b := by
  calc
    (Smat S a * Smat S b) * Smat S a = Smat S a * (Smat S b * Smat S a) := by noncomm_ring
    _ = Smat S a * (-(Smat S a * Smat S b)) := by rw [hSanti b a hab.symm]
    _ = -(Smat S a * (Smat S a * Smat S b)) := by rw [mul_neg]
    _ = -(Smat S a * Smat S a * Smat S b) := by
        rw [show Smat S a * (Smat S a * Smat S b) = Smat S a * Smat S a * Smat S b
          by noncomm_ring]
    _ = -Smat S b := by rw [hSsq a, one_mul]

private lemma smat_pair_mul_right (S : ZMod 5 → GL (Fin 2 ⊕ Fin 2) K)
    (hSsq : ∀ i, Smat S i * Smat S i = 1)
    {a b : ZMod 5} :
    (Smat S a * Smat S b) * Smat S b = Smat S a := by
  calc
    (Smat S a * Smat S b) * Smat S b = Smat S a * (Smat S b * Smat S b) := by noncomm_ring
    _ = Smat S a := by rw [hSsq b, mul_one]

private lemma smat_anti_left (S : ZMod 5 → GL (Fin 2 ⊕ Fin 2) K)
    (hSsq : ∀ i, Smat S i * Smat S i = 1)
    (hSanti : ∀ i j, i ≠ j → Smat S i * Smat S j = -(Smat S j * Smat S i))
    {a b : ZMod 5} (hab : a ≠ b) :
    Smat S a * (Smat S a * Smat S b) = -((Smat S a * Smat S b) * Smat S a) := by
  have h1 : Smat S a * (Smat S a * Smat S b) = Smat S b := by
    calc
      Smat S a * (Smat S a * Smat S b) = Smat S a * Smat S a * Smat S b := by noncomm_ring
      _ = Smat S b := by rw [hSsq a, one_mul]
  rw [h1, smat_pair_mul_left S hSsq hSanti hab, neg_neg]

private lemma smat_anti_right (S : ZMod 5 → GL (Fin 2 ⊕ Fin 2) K)
    (hSsq : ∀ i, Smat S i * Smat S i = 1)
    (hSanti : ∀ i j, i ≠ j → Smat S i * Smat S j = -(Smat S j * Smat S i))
    {a b : ZMod 5} (hab : a ≠ b) :
    Smat S b * (Smat S a * Smat S b) = -((Smat S a * Smat S b) * Smat S b) := by
  have h1 : Smat S b * (Smat S a * Smat S b) = -Smat S a := by
    calc
      Smat S b * (Smat S a * Smat S b) = (Smat S b * Smat S a) * Smat S b := by noncomm_ring
      _ = (-(Smat S a * Smat S b)) * Smat S b := by rw [hSanti b a hab.symm]
      _ = -(Smat S a * Smat S b * Smat S b) := by rw [neg_mul]
      _ = -(Smat S a * (Smat S b * Smat S b)) := by rw [mul_assoc]
      _ = -Smat S a := by rw [hSsq b, mul_one]
  rw [h1, smat_pair_mul_right S hSsq (a := a) (b := b)]

private lemma add_one_mul_half (h2 : (2 : K) ≠ 0)
    {U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hU : U * U = -1) :
    (1 + U) * ((2⁻¹ : K) • (1 - U)) = 1 := by
  rw [Matrix.mul_smul]
  have hpair : (1 + U) * (1 - U) =
      (2 : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    calc (1 + U) * (1 - U) = 1 - U * U := by noncomm_ring
      _ = 1 - (-1) := by rw [hU]
      _ = 1 + 1 := by rw [sub_neg_eq_add]
      _ = (2 : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
          (two_smul K (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)).symm
  rw [hpair, smul_smul, inv_mul_cancel₀ h2, one_smul]

private lemma half_mul_add_one (h2 : (2 : K) ≠ 0)
    {U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hU : U * U = -1) :
    ((2⁻¹ : K) • (1 - U)) * (1 + U) = 1 := by
  rw [Matrix.smul_mul]
  have hpair : (1 - U) * (1 + U) =
      (2 : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    calc (1 - U) * (1 + U) = 1 - U * U := by noncomm_ring
      _ = 1 - (-1) := by rw [hU]
      _ = 1 + 1 := by rw [sub_neg_eq_add]
      _ = (2 : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
          (two_smul K (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)).symm
  rw [hpair, smul_smul, inv_mul_cancel₀ h2, one_smul]

private def TU (h2 : (2 : K) ≠ 0) (U : GL (Fin 2 ⊕ Fin 2) K)
    (hU : ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1) :
    GL (Fin 2 ⊕ Fin 2) K :=
  ⟨1 + (U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
    (2⁻¹ : K) • (1 - (U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)),
    add_one_mul_half h2 hU, half_mul_add_one h2 hU⟩

private lemma TU_val (h2 : (2 : K) ≠ 0) (U : GL (Fin 2 ⊕ Fin 2) K)
    (hU : ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1) :
    ((TU h2 U hU : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      1 + (U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := rfl

private lemma add_one_conj_comm (h2 : (2 : K) ≠ 0)
    {U X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hU : U * U = -1)
    (hXU : X * U = U * X) :
    (1 + U) * X * ((2⁻¹ : K) • (1 - U)) = X := by
  rw [Matrix.mul_smul]
  have hpair : (1 + U) * (1 - U) =
      (2 : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    calc (1 + U) * (1 - U) = 1 - U * U := by noncomm_ring
      _ = 1 - (-1) := by rw [hU]
      _ = 1 + 1 := by rw [sub_neg_eq_add]
      _ = (2 : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
          (two_smul K (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)).symm
  have hX1U : X * (1 + U) = (1 + U) * X := by
    rw [show X * (1 + U) = X + X * U by noncomm_ring,
      show (1 + U) * X = X + U * X by noncomm_ring, hXU]
  have h1 : (1 + U) * X * (1 - U) = (2 : K) • X := by
    rw [show (1 + U) * X * (1 - U) = (X * (1 + U)) * (1 - U) by rw [hX1U],
      mul_assoc, hpair, Matrix.mul_smul, Matrix.mul_one]
  rw [h1, smul_smul, inv_mul_cancel₀ h2, one_smul]

private lemma add_one_conj_anti (h2 : (2 : K) ≠ 0)
    {U X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hU : U * U = -1)
    (hXU : X * U = -(U * X)) :
    (1 + U) * X * ((2⁻¹ : K) • (1 - U)) = U * X := by
  rw [Matrix.mul_smul]
  have hsquare : (1 + U) * (1 + U) = (2 : K) • U := by
    calc (1 + U) * (1 + U) = 1 + (U + U) + U * U := by noncomm_ring
      _ = 1 + (U + U) + (-1) := by rw [hU]
      _ = U + U := by abel
      _ = (2 : K) • U := (two_smul K U).symm
  have hX1mU : X * (1 - U) = (1 + U) * X := by
    rw [show X * (1 - U) = X - X * U by noncomm_ring,
      show (1 + U) * X = X + U * X by noncomm_ring, hXU, sub_neg_eq_add]
  have h1 : (1 + U) * X * (1 - U) = (2 : K) • (U * X) := by
    rw [show (1 + U) * X * (1 - U) = (1 + U) * (X * (1 - U)) by noncomm_ring, hX1mU,
      ← mul_assoc, hsquare, Matrix.smul_mul]
  rw [h1, smul_smul, inv_mul_cancel₀ h2, one_smul]

private lemma conj_three (T1 T2 T3 X : GL (Fin 2 ⊕ Fin 2) K) :
    (T3 * T2 * T1) * X * (T3 * T2 * T1)⁻¹ =
      T3 * (T2 * (T1 * X * T1⁻¹) * T2⁻¹) * T3⁻¹ := by
  group

private lemma mul_smul_spJ_mul (c : K) (A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    A * (c • spJ) * B = c • (A * spJ * B) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

private lemma smul_transpose_spJ (c : K) (Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    (c • Q)ᵀ * spJ * (c • Q) = (c * c) • (Qᵀ * spJ * Q) := by
  rw [Matrix.transpose_smul]
  calc (c • Qᵀ) * spJ * (c • Q)
      = ((c • (Qᵀ * spJ)) * (c • Q)) := by rw [Matrix.smul_mul]
    _ = c • ((Qᵀ * spJ) * (c • Q)) := by rw [Matrix.smul_mul]
    _ = c • (c • ((Qᵀ * spJ) * Q)) := by
          congr 1
          rw [Matrix.mul_smul]
    _ = (c * c) • (Qᵀ * spJ * Q) := by rw [smul_smul]

private lemma transpose_mul_spJ_mul (A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    (A * B)ᵀ * spJ * (A * B) = Bᵀ * (Aᵀ * spJ * A) * B := by
  rw [Matrix.transpose_mul]
  noncomm_ring

private lemma transpose_mul_spJ_of_sq {U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hUsp : Uᵀ * spJ * U = spJ) (hU2 : U * U = -1) :
    Uᵀ * spJ = -(spJ * U) := by
  have hUU : U * (-U) = 1 := by rw [mul_neg, hU2, neg_neg]
  calc Uᵀ * spJ = Uᵀ * spJ * (U * (-U)) := by rw [hUU, mul_one]
    _ = (Uᵀ * spJ * U) * (-U) := by noncomm_ring
    _ = spJ * (-U) := by rw [hUsp]
    _ = -(spJ * U) := by rw [mul_neg]

private lemma TU_transpose_spJ (h2 : (2 : K) ≠ 0) (U : GL (Fin 2 ⊕ Fin 2) K)
    (hU : ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1)
    (hUsp : (((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      spJ * ((U : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = spJ) :
    (((TU h2 U hU : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))ᵀ * spJ *
      (((TU h2 U hU : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = (2 : K) • spJ := by
  rw [TU_val]
  have hUJ := transpose_mul_spJ_of_sq hUsp hU
  have htrans : (1 + (U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))ᵀ =
      1 + ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_one]
  rw [htrans]
  have hexp : (1 + ((U : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ) * spJ *
        (1 + (U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) =
      spJ + ((U : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spJ +
        spJ * (U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) +
        ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
          spJ * (U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    noncomm_ring
  rw [hexp, hUsp, hUJ, two_smul K spJ]
  abel

private lemma TU_conj_comm (h2 : (2 : K) ≠ 0) (U : GL (Fin 2 ⊕ Fin 2) K)
    (hU : ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1)
    (X : GL (Fin 2 ⊕ Fin 2) K)
    (hXU : ((X : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((X : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    TU h2 U hU * X * (TU h2 U hU)⁻¹ = X := by
  apply Units.ext
  show (1 + (U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
      (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((2⁻¹ : K) • (1 - (U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) =
    (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  exact add_one_conj_comm h2 hU hXU

private lemma TU_conj_anti (h2 : (2 : K) ≠ 0) (U : GL (Fin 2 ⊕ Fin 2) K)
    (hU : ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1)
    (X : GL (Fin 2 ⊕ Fin 2) K)
    (hXU : ((X : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((X : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) :
    TU h2 U hU * X * (TU h2 U hU)⁻¹ = U * X := by
  apply Units.ext
  show (1 + (U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
      (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((2⁻¹ : K) • (1 - (U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) =
    ((U : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  exact add_one_conj_anti h2 hU hXU

private lemma scalar_eq_one_or_neg_one {c : Kˣ} (h : c ^ 2 = 1) : c = 1 ∨ c = -1 := by
  have hK : ((c : K) - 1) * ((c : K) + 1) = 0 := by
    have h' : (c : K) ^ 2 = 1 := by simpa using congrArg Units.val h
    linear_combination h'
  rcases mul_eq_zero.mp hK with h1 | h1
  · left
    apply Units.ext
    simpa using sub_eq_zero.mp h1
  · right
    apply Units.ext
    have h2 : (c : K) = -1 := by linear_combination h1
    rw [Units.val_neg, Units.val_one]
    exact h2

private lemma scalar_mul_coe (c : Kˣ) (X : GL (Fin 2 ⊕ Fin 2) K) :
    (((Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c * X :
      GL (Fin 2 ⊕ Fin 2) K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (c : K) • (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  rw [show (diagonal (fun _ : Fin 2 ⊕ Fin 2 => (c : K))) =
      (c : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h]]
  rw [Matrix.smul_mul, Matrix.one_mul]

private lemma scalar_neg_one :
    Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (-1 : Kˣ) =
      (-1 : GL (Fin 2 ⊕ Fin 2) K) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  by_cases h : i = j <;> simp [h]

private lemma four_ne_zero (h2 : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have h : (4 : K) = 2 * 2 := by norm_num
  rw [h]
  exact mul_ne_zero h2 h2

theorem sp4_false_of_conj_eq_sq {K : Type} [Field K] (hK : ringChar K ≠ 2)
    (h2 : ¬ IsSquare (2 : K)) {Γ : Type*} [Group Γ] [Finite Γ] (ρ : Γ →* GL (Fin 2 ⊕ Fin 2) K)
    (hρ : Function.Injective ρ) (hSp : ∀ g, ρ g ∈ StatedSp 2 K) {N : Subgroup Γ}
    (hN : IsQuatType ρ N)
    (hcard : Nat.card N = 16 * Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ))
    {c g : Γ} (hc : orderOf c = 5) (hg : g * c * g⁻¹ * (c ^ 2)⁻¹ ∈ N) : False := by
  classical
  let Z : Subgroup Γ := (StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ
  have h2K : (2 : K) ≠ 0 := fun h0 => h2 ⟨0, by rw [h0, mul_zero]⟩
  have hcardZ : Nat.card N = 16 * Nat.card Z := hcard
  have hSpJ : ∀ u : Γ,
      (((ρ u : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))ᵀ * spJ *
        (((ρ u : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = spJ := by
    intro u
    have h := hSp u
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff] at h
    simpa [spJ] using h
  have hNZ : ¬ N ≤ Z := by
    intro hle
    have heq : N = Z := le_antisymm hle hN.scalars_le
    have hpos : 0 < Nat.card Z := Nat.card_pos
    have h : Nat.card Z = 16 * Nat.card Z := by
      have h' := hcardZ
      rw [heq] at h'
      exact h'
    omega
  obtain ⟨x, hxN, hxZ⟩ := Set.not_subset.mp (show ¬ (N : Set Γ) ⊆ (Z : Set Γ) from hNZ)
  have hy : ∃ y ∈ N, x * y ≠ y * x := by
    by_contra h
    have h' : ∀ y, y ∈ N → x * y = y * x := by
      intro y hy'
      by_contra hne
      exact h ⟨y, hy', hne⟩
    exact hxZ (hN.mem_of_comm x hxN h')
  obtain ⟨y, hyN, hxy_ne⟩ := hy
  have hanti : ((ρ (x * y) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((ρ (y * x) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
    rcases hN.comm_or_anticomm x hxN y hyN with hc' | hc'
    · exact absurd hc' hxy_ne
    · exact hc'
  let z0 : Γ := x * y * x⁻¹ * y⁻¹
  have hxyunit : ρ x * ρ y = -(ρ y * ρ x) := by
    apply Units.ext
    simpa [map_mul] using hanti
  have hz0val : ρ z0 = ρ x * ρ y * (ρ x)⁻¹ * (ρ y)⁻¹ := by
    simp only [z0, map_mul, map_inv]
  have hz0unit : ρ z0 = -1 := by
    rw [hz0val, hxyunit]
    have h1 : (-(ρ y * ρ x)) * (ρ x)⁻¹ * (ρ y)⁻¹ =
        -((ρ y * ρ x) * (ρ x)⁻¹ * (ρ y)⁻¹) := by
      have hA : (-(ρ y * ρ x)) * (ρ x)⁻¹ = -((ρ y * ρ x) * (ρ x)⁻¹) := by
        rw [← gl_neg_mul]
      have hB : (-((ρ y * ρ x) * (ρ x)⁻¹)) * (ρ y)⁻¹ =
          -(((ρ y * ρ x) * (ρ x)⁻¹) * (ρ y)⁻¹) := by rw [← gl_neg_mul]
      rw [hA, hB]
    have h2 : (ρ y * ρ x) * (ρ x)⁻¹ * (ρ y)⁻¹ = 1 := by group
    rw [h1, h2]
  have hz0mem : z0 ∈ Z := by
    show ρ z0 ∈ StatedScalars (Fin 2 ⊕ Fin 2) K
    rw [hz0unit]
    exact ⟨-1, scalar_neg_one⟩
  have hz0ne : z0 ≠ 1 := by
    intro h
    have h' : ρ z0 = 1 := by rw [h, map_one]
    rw [hz0unit] at h'
    have hmat : (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 :=
      congrArg (fun u : GL (Fin 2 ⊕ Fin 2) K =>
        (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h'
    have hentry := congrFun (congrFun hmat (Sum.inl 0)) (Sum.inl 0)
    simp [Matrix.neg_apply] at hentry
    exact Ring.neg_one_ne_one_of_char_ne_two hK hentry
  have hZset : ∀ w : Γ, w ∈ Z ↔ w = 1 ∨ w = z0 := by
    intro w
    constructor
    · intro hw
      have hw' : ρ w ∈ StatedScalars (Fin 2 ⊕ Fin 2) K := hw
      obtain ⟨u, hu⟩ := hw'
      have hspu : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) u ∈ StatedSp 2 K := by
        rw [hu]
        exact hSp w
      have hu2 : u ^ 2 = 1 :=
        (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff (n := 2) (by norm_num) u).1 hspu
      rcases scalar_eq_one_or_neg_one hu2 with hu1 | hu1
      · left
        apply hρ
        rw [← hu, hu1]
        simp
      · right
        refine hρ ?_
        rw [← hu, hu1, scalar_neg_one, hz0unit]
    · rintro (rfl | rfl)
      · exact Z.one_mem
      · exact hz0mem
  have hz0sq : z0 * z0 = 1 := by
    apply hρ
    have h' : ρ (z0 * z0) = 1 := by
      rw [map_mul, hz0unit]
      simp
    simpa using h'
  have hZeq : Z = Subgroup.zpowers z0 := by
    apply le_antisymm
    · intro w hw
      rcases (hZset w).1 hw with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers z0
    · rw [Subgroup.zpowers_le]
      exact hz0mem
  have hZcard : Nat.card Z = 2 := by
    rw [hZeq, Nat.card_zpowers]
    exact orderOf_eq_prime (hp := ⟨by norm_num⟩) (by rwa [pow_two]) hz0ne
  have hNcard : Nat.card N = 32 := by
    rw [hcardZ, hZcard]
  have hZ2 : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)
  have hz0mat : (((ρ z0 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
    rw [hz0unit]
    rfl
  have hzc0 : ∀ u : Γ, u * z0 = z0 * u := by
    intro u
    apply hρ
    calc ρ (u * z0) = ρ u * ρ z0 := map_mul ρ u z0
      _ = ρ u * (-1) := by rw [hz0unit]
      _ = (-1) * ρ u := by rw [gl_neg_mul_neg_one, gl_neg_one_mul]
      _ = ρ z0 * ρ u := by rw [hz0unit]
      _ = ρ (z0 * u) := (map_mul ρ z0 u).symm
  have hzc : ∀ z ∈ Z, ∀ u : Γ, u * z = z * u := by
    intro z hz u
    rcases (hZset z).1 hz with rfl | rfl
    · rw [one_mul, mul_one]
    · exact hzc0 u
  have hcardι : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
  have hι : (Fintype.card (Fin 2 ⊕ Fin 2) : K) ≠ 0 := by
    rw [hcardι]
    exact four_ne_zero h2K
  have hcard' : Nat.card N = Fintype.card (Fin 2 ⊕ Fin 2) ^ 2 * Nat.card Z := by
    rw [hcardι, hcardZ]
    norm_num
  have hspan : Submodule.span K (Set.range fun u : N =>
      ((ρ (u : Γ) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = ⊤ :=
    span_eq_top_of_isQuatType hK hι ρ hρ hN hcard'
  have hker : ∀ u : Γ, (∀ v ∈ N, u * v * u⁻¹ * v⁻¹ ∈ Z) → u ∈ N := by
    intro u hu
    obtain ⟨y, hyN', hyZ⟩ :=
      exists_mem_mul_inv_mem_scalars hK hι ρ hρ hN hspan (ρ u) (by
        intro v hv
        have h := hu v hv
        have h' : ρ (u * v * u⁻¹ * v⁻¹) ∈ StatedScalars (Fin 2 ⊕ Fin 2) K := h
        simpa [map_mul, map_inv] using h')
    have hmem : u * y⁻¹ ∈ Z := by
      show ρ (u * y⁻¹) ∈ StatedScalars (Fin 2 ⊕ Fin 2) K
      rw [map_mul, map_inv]
      exact hyZ
    have hueq : u = (u * y⁻¹) * y := by group
    rw [hueq]
    exact Subgroup.mul_mem _ (hN.scalars_le hmem) hyN'
  have hfree : ∀ v ∈ N, c * v * c⁻¹ * v⁻¹ ∈ Z → v ∈ Z := by
    intro v hv hcv
    exact @mem_of_orderOf_five_of_conj Γ _ _ Z N hN.normal hN.scalars_le hzc hZ2 hcardZ
      hN.sq_mem hker c hc v hv hcv
  have hcomm : ∀ v ∈ N, ∀ w ∈ N, v * w = w * v ∨ v * w = z0 * (w * v) := by
    intro v hv w hw
    rcases hN.comm_or_anticomm v hv w hw with h | h
    · exact Or.inl h
    · right
      apply hρ
      apply Units.ext
      calc ((ρ (v * w) : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
          = -(((ρ (w * v) : GL (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := h
        _ = (((ρ z0 : GL (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
              (((ρ (w * v) : GL (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
            rw [hz0mat, neg_one_mul]
        _ = (((ρ (z0 * (w * v)) : GL (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :=
            congrArg (fun u : GL (Fin 2 ⊕ Fin 2) K =>
              (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
              (map_mul ρ z0 (w * v)).symm
  have hcen : ∀ v ∈ N, (∀ w ∈ N, v * w = w * v) → v ∈ Z := hN.mem_of_comm
  have hts : ∀ v ∈ N, ∀ w ∈ N, v * v = 1 → w * w = 1 → v * w = w * v →
      v ∈ Z ∨ w ∈ Z ∨ v * w ∈ Z := by
    intro v hv w hw hv2 hw2 hvw
    rcases sp_mem_scalars_of_commute hK ρ hρ hSp hN hv hw hv2 hw2 hvw with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨s, hsN, hs2, hsanti, hgs, hspan_s⟩ :=
    @exists_five_singular Γ _ _ Z N hN.normal z0 hZset hz0ne hzc0 hN.scalars_le hNcard
      hN.sq_mem hcomm hcen hts c g hc hfree hg
  let S : ZMod 5 → GL (Fin 2 ⊕ Fin 2) K := fun i => ρ (s i)
  have hSsq : ∀ i, Smat S i * Smat S i = 1 := by
    intro i
    have h : S i * S i = 1 := by
      show ρ (s i) * ρ (s i) = 1
      rw [← map_mul, hs2 i, map_one]
    have h'' : ((S i * S i : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by rw [h]; rfl
    simpa [Smat] using h''
  have hSanti : ∀ i j, i ≠ j → Smat S i * Smat S j = -(Smat S j * Smat S i) := by
    intro i j hij
    have h : S i * S j = -(S j * S i) := by
      calc S i * S j = ρ (s i * s j) := (map_mul ρ (s i) (s j)).symm
        _ = ρ (z0 * (s j * s i)) := by rw [hsanti i j hij]
        _ = ρ z0 * ρ (s j * s i) := map_mul ρ z0 (s j * s i)
        _ = (-1) * (S j * S i) := by rw [hz0unit, map_mul]
        _ = -(S j * S i) := gl_neg_one_mul _
    have h' := congrArg (fun u : GL (Fin 2 ⊕ Fin 2) K =>
      (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
    simpa [Smat] using h'
  let U1 : GL (Fin 2 ⊕ Fin 2) K := S 1 * S 2
  let U2 : GL (Fin 2 ⊕ Fin 2) K := S 1 * S 4
  let U3 : GL (Fin 2 ⊕ Fin 2) K := S 1 * S 3
  have hU1sq : (((U1 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (((U1 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
    simpa [U1] using smat_pair_sq S hSsq hSanti (a := (1 : ZMod 5)) (b := (2 : ZMod 5))
      (by decide)
  have hU2sq : (((U2 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (((U2 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
    simpa [U2] using smat_pair_sq S hSsq hSanti (a := (1 : ZMod 5)) (b := (4 : ZMod 5))
      (by decide)
  have hU3sq : (((U3 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (((U3 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
    simpa [U3] using smat_pair_sq S hSsq hSanti (a := (1 : ZMod 5)) (b := (3 : ZMod 5))
      (by decide)
  have hU1sp : (((U1 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spJ *
      (((U1 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = spJ := by
    have h := hSp (s 1 * s 2)
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff] at h
    have hU1eq : U1 = ρ (s 1 * s 2) := by
      change S 1 * S 2 = ρ (s 1 * s 2)
      rw [map_mul]
    rw [hU1eq]
    simpa [spJ] using h
  have hU2sp : (((U2 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spJ *
      (((U2 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = spJ := by
    have h := hSp (s 1 * s 4)
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff] at h
    have hU2eq : U2 = ρ (s 1 * s 4) := by
      change S 1 * S 4 = ρ (s 1 * s 4)
      rw [map_mul]
    rw [hU2eq]
    simpa [spJ] using h
  have hU3sp : (((U3 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spJ *
      (((U3 : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = spJ := by
    have h := hSp (s 1 * s 3)
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff] at h
    have hU3eq : U3 = ρ (s 1 * s 3) := by
      change S 1 * S 3 = ρ (s 1 * s 3)
      rw [map_mul]
    rw [hU3eq]
    simpa [spJ] using h
  have hc10 : Smat S 0 * ((U1 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((U1 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 0 := by
    simpa [U1, Smat] using smat_comm_pair S hSanti (a := (1 : ZMod 5)) (b := (2 : ZMod 5))
      (c := (0 : ZMod 5)) (by decide) (by decide)
  have hc13 : Smat S 3 * ((U1 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((U1 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 3 := by
    simpa [U1, Smat] using smat_comm_pair S hSanti (a := (1 : ZMod 5)) (b := (2 : ZMod 5))
      (c := (3 : ZMod 5)) (by decide) (by decide)
  have hc14 : Smat S 4 * ((U1 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((U1 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 4 := by
    simpa [U1, Smat] using smat_comm_pair S hSanti (a := (1 : ZMod 5)) (b := (2 : ZMod 5))
      (c := (4 : ZMod 5)) (by decide) (by decide)
  have ha11 : Smat S 1 * ((U1 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((U1 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 1) := by
    simpa [U1, Smat] using smat_anti_left S hSsq hSanti (a := (1 : ZMod 5)) (b := (2 : ZMod 5))
      (by decide)
  have ha12 : Smat S 2 * ((U1 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((U1 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 2) := by
    simpa [U1, Smat] using smat_anti_right S hSsq hSanti (a := (1 : ZMod 5)) (b := (2 : ZMod 5))
      (by decide)
  have hc20 : Smat S 0 * ((U2 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((U2 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 0 := by
    simpa [U2, Smat] using smat_comm_pair S hSanti (a := (1 : ZMod 5)) (b := (4 : ZMod 5))
      (c := (0 : ZMod 5)) (by decide) (by decide)
  have hc22 : Smat S 2 * ((U2 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((U2 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 2 := by
    simpa [U2, Smat] using smat_comm_pair S hSanti (a := (1 : ZMod 5)) (b := (4 : ZMod 5))
      (c := (2 : ZMod 5)) (by decide) (by decide)
  have hc23 : Smat S 3 * ((U2 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((U2 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 3 := by
    simpa [U2, Smat] using smat_comm_pair S hSanti (a := (1 : ZMod 5)) (b := (4 : ZMod 5))
      (c := (3 : ZMod 5)) (by decide) (by decide)
  have ha21 : Smat S 1 * ((U2 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((U2 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 1) := by
    simpa [U2, Smat] using smat_anti_left S hSsq hSanti (a := (1 : ZMod 5)) (b := (4 : ZMod 5))
      (by decide)
  have ha24 : Smat S 4 * ((U2 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((U2 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 4) := by
    simpa [U2, Smat] using smat_anti_right S hSsq hSanti (a := (1 : ZMod 5)) (b := (4 : ZMod 5))
      (by decide)
  have hc30 : Smat S 0 * ((U3 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((U3 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 0 := by
    simpa [U3, Smat] using smat_comm_pair S hSanti (a := (1 : ZMod 5)) (b := (3 : ZMod 5))
      (c := (0 : ZMod 5)) (by decide) (by decide)
  have hc32 : Smat S 2 * ((U3 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((U3 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 2 := by
    simpa [U3, Smat] using smat_comm_pair S hSanti (a := (1 : ZMod 5)) (b := (3 : ZMod 5))
      (c := (2 : ZMod 5)) (by decide) (by decide)
  have hc34 : Smat S 4 * ((U3 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((U3 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 4 := by
    simpa [U3, Smat] using smat_comm_pair S hSanti (a := (1 : ZMod 5)) (b := (3 : ZMod 5))
      (c := (4 : ZMod 5)) (by decide) (by decide)
  have ha31 : Smat S 1 * ((U3 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((U3 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 1) := by
    simpa [U3, Smat] using smat_anti_left S hSsq hSanti (a := (1 : ZMod 5)) (b := (3 : ZMod 5))
      (by decide)
  have ha33 : Smat S 3 * ((U3 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((U3 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Smat S 3) := by
    simpa [U3, Smat] using smat_anti_right S hSsq hSanti (a := (1 : ZMod 5)) (b := (3 : ZMod 5))
      (by decide)
  let T1 : GL (Fin 2 ⊕ Fin 2) K := TU h2K U1 hU1sq
  let T2 : GL (Fin 2 ⊕ Fin 2) K := TU h2K U2 hU2sq
  let T3 : GL (Fin 2 ⊕ Fin 2) K := TU h2K U3 hU3sq
  let T : GL (Fin 2 ⊕ Fin 2) K := T3 * T2 * T1
  have hfix10 : T1 * S 0 * T1⁻¹ = S 0 :=
    TU_conj_comm h2K U1 hU1sq (S 0) hc10
  have hfix13 : T1 * S 3 * T1⁻¹ = S 3 :=
    TU_conj_comm h2K U1 hU1sq (S 3) hc13
  have hfix14 : T1 * S 4 * T1⁻¹ = S 4 :=
    TU_conj_comm h2K U1 hU1sq (S 4) hc14
  have hfix20 : T2 * S 0 * T2⁻¹ = S 0 :=
    TU_conj_comm h2K U2 hU2sq (S 0) hc20
  have hfix22 : T2 * S 2 * T2⁻¹ = S 2 :=
    TU_conj_comm h2K U2 hU2sq (S 2) hc22
  have hfix23 : T2 * S 3 * T2⁻¹ = S 3 :=
    TU_conj_comm h2K U2 hU2sq (S 3) hc23
  have hfix30 : T3 * S 0 * T3⁻¹ = S 0 :=
    TU_conj_comm h2K U3 hU3sq (S 0) hc30
  have hfix32 : T3 * S 2 * T3⁻¹ = S 2 :=
    TU_conj_comm h2K U3 hU3sq (S 2) hc32
  have hfix34 : T3 * S 4 * T3⁻¹ = S 4 :=
    TU_conj_comm h2K U3 hU3sq (S 4) hc34
  have hstep11 : T1 * S 1 * T1⁻¹ = U1 * S 1 :=
    TU_conj_anti h2K U1 hU1sq (S 1) ha11
  have hstep12 : T1 * S 2 * T1⁻¹ = U1 * S 2 :=
    TU_conj_anti h2K U1 hU1sq (S 2) ha12
  have hstep21 : T2 * S 1 * T2⁻¹ = U2 * S 1 :=
    TU_conj_anti h2K U2 hU2sq (S 1) ha21
  have hstep24 : T2 * S 4 * T2⁻¹ = U2 * S 4 :=
    TU_conj_anti h2K U2 hU2sq (S 4) ha24
  have hstep31 : T3 * S 1 * T3⁻¹ = U3 * S 1 :=
    TU_conj_anti h2K U3 hU3sq (S 1) ha31
  have hstep33 : T3 * S 3 * T3⁻¹ = U3 * S 3 :=
    TU_conj_anti h2K U3 hU3sq (S 3) ha33
  have hU1S1 : U1 * S 1 = -S 2 := by
    have h := smat_pair_mul_left S hSsq hSanti (a := (1 : ZMod 5)) (b := (2 : ZMod 5))
      (by decide)
    apply Units.ext
    simpa [U1, Smat, Units.val_neg] using h
  have hU1S2 : U1 * S 2 = S 1 := by
    have h := smat_pair_mul_right S hSsq (a := (1 : ZMod 5)) (b := (2 : ZMod 5))
    apply Units.ext
    simpa [U1, Smat] using h
  have hU2S1 : U2 * S 1 = -S 4 := by
    have h := smat_pair_mul_left S hSsq hSanti (a := (1 : ZMod 5)) (b := (4 : ZMod 5))
      (by decide)
    apply Units.ext
    simpa [U2, Smat, Units.val_neg] using h
  have hU2S4 : U2 * S 4 = S 1 := by
    have h := smat_pair_mul_right S hSsq (a := (1 : ZMod 5)) (b := (4 : ZMod 5))
    apply Units.ext
    simpa [U2, Smat] using h
  have hU3S1 : U3 * S 1 = -S 3 := by
    have h := smat_pair_mul_left S hSsq hSanti (a := (1 : ZMod 5)) (b := (3 : ZMod 5))
      (by decide)
    apply Units.ext
    simpa [U3, Smat, Units.val_neg] using h
  have hU3S3 : U3 * S 3 = S 1 := by
    have h := smat_pair_mul_right S hSsq (a := (1 : ZMod 5)) (b := (3 : ZMod 5))
    apply Units.ext
    simpa [U3, Smat] using h
  have hTval : T = T3 * T2 * T1 := rfl
  have hT0 : T * S 0 * T⁻¹ = S 0 := by
    rw [hTval, conj_three, hfix10, hfix20, hfix30]
  have hT1f : T * S 1 * T⁻¹ = -S 2 := by
    rw [hTval, conj_three, hstep11, hU1S1]
    rw [show T2 * (-S 2) * T2⁻¹ = -S 2 from by rw [gl_conj_neg, hfix22]]
    rw [show T3 * (-S 2) * T3⁻¹ = -S 2 from by rw [gl_conj_neg, hfix32]]
  have hT2f : T * S 2 * T⁻¹ = -S 4 := by
    rw [hTval, conj_three, hstep12, hU1S2, hstep21, hU2S1]
    rw [show T3 * (-S 4) * T3⁻¹ = -S 4 from by rw [gl_conj_neg, hfix34]]
  have hT3f : T * S 3 * T⁻¹ = S 1 := by
    rw [hTval, conj_three, hfix13, hfix23, hstep33, hU3S3]
  have hT4f : T * S 4 * T⁻¹ = -S 3 := by
    rw [hTval, conj_three, hfix14, hstep24, hU2S4, hstep31, hU3S1]
  have hT : ∀ i : ZMod 5, T * S i * T⁻¹ = S (2 * i) ∨
      T * S i * T⁻¹ = -(S (2 * i)) := by
    intro i
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      revert i
      decide
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · left
      have h20 : (2 : ZMod 5) * 0 = 0 := by decide
      simpa [h20] using hT0
    · right
      have h21 : (2 : ZMod 5) * 1 = 2 := by decide
      simpa [h21] using hT1f
    · right
      have h22 : (2 : ZMod 5) * 2 = 4 := by decide
      simpa [h22] using hT2f
    · left
      have h23 : (2 : ZMod 5) * 3 = 1 := by decide
      simpa [h23] using hT3f
    · right
      have h24 : (2 : ZMod 5) * 4 = 3 := by decide
      simpa [h24] using hT4f
  have hTsp : (((T : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spJ *
      (((T : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (8 : K) • spJ := by
    let T1m : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      ((T1 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    let T2m : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      ((T2 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    let T3m : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      ((T3 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    have h1 : T1mᵀ * spJ * T1m = (2 : K) • spJ :=
      TU_transpose_spJ h2K U1 hU1sq hU1sp
    have h2' : T2mᵀ * spJ * T2m = (2 : K) • spJ :=
      TU_transpose_spJ h2K U2 hU2sq hU2sp
    have h3 : T3mᵀ * spJ * T3m = (2 : K) • spJ :=
      TU_transpose_spJ h2K U3 hU3sq hU3sp
    have hTm : (((T : GL (Fin 2 ⊕ Fin 2) K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = T3m * T2m * T1m := rfl
    rw [hTm, Matrix.transpose_mul, Matrix.transpose_mul]
    change (T1mᵀ * (T2mᵀ * T3mᵀ)) * spJ * ((T3m * T2m) * T1m) = (8 : K) • spJ
    calc
      (T1mᵀ * (T2mᵀ * T3mᵀ)) * spJ * ((T3m * T2m) * T1m)
          = T1mᵀ * T2mᵀ * (T3mᵀ * spJ * T3m) * T2m * T1m := by noncomm_ring
      _ = T1mᵀ * T2mᵀ * ((2 : K) • spJ) * T2m * T1m := by rw [h3]
      _ = (2 : K) • (T1mᵀ * (T2mᵀ * spJ * T2m) * T1m) := by
            rw [show T1mᵀ * T2mᵀ * ((2 : K) • spJ) * T2m * T1m =
                (T1mᵀ * T2mᵀ) * ((2 : K) • spJ) * (T2m * T1m) by noncomm_ring,
              mul_smul_spJ_mul]
            congr 1
            noncomm_ring
      _ = (2 : K) • (T1mᵀ * ((2 : K) • spJ) * T1m) := by rw [h2']
      _ = ((2 : K) * (2 : K)) • (T1mᵀ * spJ * T1m) := by
            rw [mul_smul_spJ_mul, smul_smul]
      _ = ((2 : K) * (2 : K)) • ((2 : K) • spJ) := by rw [h1]
      _ = (((2 : K) * (2 : K)) * (2 : K)) • spJ := by rw [smul_smul]
      _ = (8 : K) • spJ := by
            congr 1
            ring

  let A : GL (Fin 2 ⊕ Fin 2) K := T⁻¹ * ρ g
  have hg_act : ∀ i : ZMod 5, ρ g * S i * (ρ g)⁻¹ = S (2 * i) ∨
      ρ g * S i * (ρ g)⁻¹ = -(S (2 * i)) := by
    intro i
    have hmemZ := hgs i
    have hρeq : ρ (g * s i * g⁻¹ * (s (2 * i))⁻¹) =
        ρ g * S i * (ρ g)⁻¹ * (S (2 * i))⁻¹ := by
      simp [S, map_mul, map_inv]
    rcases (hZset (g * s i * g⁻¹ * (s (2 * i))⁻¹)).1 hmemZ with h1 | h1
    · left
      have hm : ρ g * S i * (ρ g)⁻¹ * (S (2 * i))⁻¹ = 1 := by
        rw [← hρeq, h1, map_one]
      calc ρ g * S i * (ρ g)⁻¹
          = (ρ g * S i * (ρ g)⁻¹ * (S (2 * i))⁻¹) * S (2 * i) := by group
        _ = 1 * S (2 * i) := by rw [hm]
        _ = S (2 * i) := one_mul _
    · right
      have hm : ρ g * S i * (ρ g)⁻¹ * (S (2 * i))⁻¹ = -1 := by
        rw [← hρeq, h1, hz0unit]
      calc ρ g * S i * (ρ g)⁻¹
          = (ρ g * S i * (ρ g)⁻¹ * (S (2 * i))⁻¹) * S (2 * i) := by group
        _ = (-1 : GL (Fin 2 ⊕ Fin 2) K) * S (2 * i) := by rw [hm]
        _ = -(S (2 * i)) := gl_neg_one_mul _
  have hT_inv : ∀ i : ZMod 5, T⁻¹ * S (2 * i) * T = S i ∨
      T⁻¹ * S (2 * i) * T = -(S i) := by
    intro i
    rcases hT i with h | h
    · left
      calc T⁻¹ * S (2 * i) * T = T⁻¹ * (T * S i * T⁻¹) * T := by rw [h]
        _ = S i := by group
    · right
      have h3 : -(T⁻¹ * S (2 * i) * T) = S i := by
        calc -(T⁻¹ * S (2 * i) * T) =
            T⁻¹ * (-(S (2 * i))) * T := (gl_inv_conj_neg T (S (2 * i))).symm
          _ = T⁻¹ * (T * S i * T⁻¹) * T := by rw [← h]
          _ = S i := by group
      calc T⁻¹ * S (2 * i) * T = -(-(T⁻¹ * S (2 * i) * T)) := (gl_neg_neg _).symm
        _ = -(S i) := by rw [h3]
  have hA_act : ∀ i : ZMod 5, A * S i * A⁻¹ = S i ∨ A * S i * A⁻¹ = -(S i) := by
    intro i
    have hAconj : A * S i * A⁻¹ = T⁻¹ * (ρ g * S i * (ρ g)⁻¹) * T := by
      simp only [A]
      group
    rcases hg_act i with hg' | hg' <;> rcases hT_inv i with hT' | hT'
    · left
      rw [hAconj, hg', hT']
    · right
      rw [hAconj, hg', hT']
    · right
      rw [hAconj, hg', gl_inv_conj_neg, hT']
    · left
      rw [hAconj, hg', gl_inv_conj_neg, hT', gl_neg_neg]
  have hA_scalars : ∀ v ∈ N,
      A * ρ v * A⁻¹ * (ρ v)⁻¹ ∈ StatedScalars (Fin 2 ⊕ Fin 2) K := by
    let H : Subgroup Γ :=
      { carrier := {v : Γ | A * ρ v * A⁻¹ * (ρ v)⁻¹ ∈ StatedScalars (Fin 2 ⊕ Fin 2) K}
        one_mem' := by
          show A * ρ 1 * A⁻¹ * (ρ 1)⁻¹ ∈ StatedScalars (Fin 2 ⊕ Fin 2) K
          rw [map_one]
          simp
        mul_mem' := by
          intro u v hu hv
          show A * ρ (u * v) * A⁻¹ * (ρ (u * v))⁻¹ ∈ StatedScalars (Fin 2 ⊕ Fin 2) K
          rw [map_mul]
          have h_eq : A * (ρ u * ρ v) * A⁻¹ * (ρ u * ρ v)⁻¹ =
              (A * ρ u * A⁻¹ * (ρ u)⁻¹) *
                (ρ u * (A * ρ v * A⁻¹ * (ρ v)⁻¹) * (ρ u)⁻¹) := by group
          rw [h_eq]
          exact Subgroup.mul_mem _ hu
            ((inferInstance : (StatedScalars (Fin 2 ⊕ Fin 2) K).Normal).conj_mem
              (A * ρ v * A⁻¹ * (ρ v)⁻¹) hv (ρ u))
        inv_mem' := by
          intro u hu
          show A * ρ u⁻¹ * A⁻¹ * (ρ u⁻¹)⁻¹ ∈ StatedScalars (Fin 2 ⊕ Fin 2) K
          rw [map_inv, inv_inv]
          have h_eq : A * (ρ u)⁻¹ * A⁻¹ * (ρ u) =
              (ρ u)⁻¹ * (A * ρ u * A⁻¹ * (ρ u)⁻¹)⁻¹ * (ρ u) := by group
          rw [h_eq]
          exact (inferInstance : (StatedScalars (Fin 2 ⊕ Fin 2) K).Normal).conj_mem
            ((A * ρ u * A⁻¹ * (ρ u)⁻¹)⁻¹)
            (Subgroup.inv_mem (StatedScalars (Fin 2 ⊕ Fin 2) K) hu) ((ρ u)⁻¹) }
    have hsH : ∀ i, s i ∈ H := by
      intro i
      rcases hA_act i with h | h
      · show A * ρ (s i) * A⁻¹ * (ρ (s i))⁻¹ ∈ StatedScalars (Fin 2 ⊕ Fin 2) K
        rw [h]
        rw [mul_inv_cancel]
        exact (StatedScalars (Fin 2 ⊕ Fin 2) K).one_mem
      · show A * ρ (s i) * A⁻¹ * (ρ (s i))⁻¹ ∈ StatedScalars (Fin 2 ⊕ Fin 2) K
        rw [h]
        have hneg : (-(S i)) * (S i)⁻¹ = -1 := by
          rw [← gl_neg_mul (S i) ((S i)⁻¹), mul_inv_cancel]
        rw [hneg]
        exact ⟨-1, scalar_neg_one⟩
    have hclosure : Subgroup.closure (Set.range s) ≤ H :=
      (Subgroup.closure_le H).mpr (by
        rintro v ⟨i, rfl⟩
        exact hsH i)
    have hNH : N ≤ H := le_trans hspan_s hclosure
    intro v hv
    exact hNH hv
  obtain ⟨y, hyN, hyA⟩ :=
    exists_mem_mul_inv_mem_scalars hK hι ρ hρ hN hspan A hA_scalars
  obtain ⟨c1, hc1⟩ := hyA
  have hcentral : T * Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c1 =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c1 * T := by
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c1 ∈
        Subgroup.center (GL (Fin 2 ⊕ Fin 2) K) := by
      rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
      exact ⟨c1, rfl⟩
    exact Subgroup.mem_center_iff.mp hmem T
  have hTg : ρ g = Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c1 * (T * ρ y) := by
    have h1 : T⁻¹ * ρ g * (ρ y)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c1 := by
      simpa [A] using hc1.symm
    calc ρ g = T * (T⁻¹ * ρ g) := by group
      _ = T * ((T⁻¹ * ρ g * (ρ y)⁻¹) * ρ y) := by group
      _ = T * (Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c1 * ρ y) := by rw [h1]
      _ = T * Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c1 * ρ y := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c1 * T * ρ y := by rw [hcentral]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c1 * (T * ρ y) := by group
  have hmat : (((ρ g : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (c1 : K) • ((((T : GL (Fin 2 ⊕ Fin 2) K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((ρ y : GL (Fin 2 ⊕ Fin 2) K)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
    have hval := congrArg (fun u : GL (Fin 2 ⊕ Fin 2) K =>
      (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hTg
    rw [scalar_mul_coe] at hval
    simpa using hval
  have hJeq : (spJ (K := K)) = (((c1 : K) * (c1 : K)) * (8 : K)) • (spJ (K := K)) := by
    let Tmat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      (((T : GL (Fin 2 ⊕ Fin 2) K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    let Ymat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      (((ρ y : GL (Fin 2 ⊕ Fin 2) K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    have hTmat : (((T : GL (Fin 2 ⊕ Fin 2) K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Tmat := rfl
    have hYmat : (((ρ y : GL (Fin 2 ⊕ Fin 2) K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Ymat := rfl
    have hTsp' : Tmatᵀ * spJ * Tmat = (8 : K) • spJ := hTsp
    have hYsp : Ymatᵀ * spJ * Ymat = spJ := hSpJ y
    have hmat' : (((ρ g : GL (Fin 2 ⊕ Fin 2) K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (c1 : K) • (Tmat * Ymat) := by
      rw [hTmat, hYmat] at hmat
      exact hmat
    calc spJ = (((ρ g : GL (Fin 2 ⊕ Fin 2) K)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spJ *
          (((ρ g : GL (Fin 2 ⊕ Fin 2) K)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := (hSpJ g).symm
      _ = ((c1 : K) • (Tmat * Ymat))ᵀ * spJ * ((c1 : K) • (Tmat * Ymat)) := by
            rw [hmat']
      _ = ((c1 : K) * (c1 : K)) • ((Tmat * Ymat)ᵀ * spJ * (Tmat * Ymat)) := by
            rw [smul_transpose_spJ]
      _ = ((c1 : K) * (c1 : K)) • (Ymatᵀ * (Tmatᵀ * spJ * Tmat) * Ymat) := by
            rw [transpose_mul_spJ_mul]
      _ = ((c1 : K) * (c1 : K)) • (Ymatᵀ * ((8 : K) • spJ) * Ymat) := by rw [hTsp']
      _ = (((c1 : K) * (c1 : K)) * (8 : K)) • (Ymatᵀ * spJ * Ymat) := by
            rw [mul_smul_spJ_mul, smul_smul]
      _ = (((c1 : K) * (c1 : K)) * (8 : K)) • spJ := by rw [hYsp]
  have h8 : (8 : K) * (c1 : K) ^ 2 = 1 := by
    have h := congrFun (congrFun hJeq (Sum.inl 0)) (Sum.inr 0)
    rw [Matrix.smul_apply, spJ_inl_zero_inr_zero, smul_eq_mul, mul_one] at h
    have h' : (c1 : K) * (c1 : K) * (8 : K) = 1 := h.symm
    calc (8 : K) * (c1 : K) ^ 2 = (c1 : K) * (c1 : K) * (8 : K) := by ring
      _ = 1 := h'
  refine h2 ⟨(4 : K) * (c1 : K), ?_⟩
  have h8' : (8 : K) * ((c1 : K) * (c1 : K)) = 1 := by simpa [sq] using h8
  rw [show (4 : K) * (c1 : K) * ((4 : K) * (c1 : K)) =
      2 * ((8 : K) * ((c1 : K) * (c1 : K))) by ring, h8']
  ring

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
