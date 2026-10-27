module

public import Mathlib

public section

open Matrix
open scoped commutatorElement

local notation "SL" => Matrix.SpecialLinearGroup

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable {n : ℕ} {k : Type*} [Field k] (hn : 3 ≤ n)




@[expose] def i0 : Fin n := ⟨0, by omega⟩
@[expose] def iL : Fin n := ⟨n - 1, by omega⟩

theorem i0_ne_iL : i0 hn ≠ iL hn := by
  simp only [i0, iL, ne_eq, Fin.mk.injEq]
  omega

@[expose] def rowMat (β : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  1 + vecMulVec (Pi.single (i0 hn) (1 : k)) β

@[expose] def colMat (v : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  1 + vecMulVec v (Pi.single (iL hn) (1 : k))

theorem det_rowMat (β : Fin n → k) (hβ : β (i0 hn) = 0) : (rowMat hn β).det = 1 := by
  rw [rowMat, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct_single, hβ]

theorem det_colMat (v : Fin n → k) (hv : v (iL hn) = 0) : (colMat hn v).det = 1 := by
  rw [colMat, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]
  simp [single_dotProduct, hv]

@[expose] def rowElt (β : Fin n → k) (hβ : β (i0 hn) = 0) : SL (Fin n) k :=
  ⟨rowMat hn β, det_rowMat hn β hβ⟩

@[expose] def colElt (v : Fin n → k) (hv : v (iL hn) = 0) : SL (Fin n) k :=
  ⟨colMat hn v, det_colMat hn v hv⟩


theorem abstract_comm {R : Type*} [Ring R] (P Q : R) (hPP : P * P = 0) (hQQ : Q * Q = 0)
    (hPQ : P * Q = 0) : (1 - P) * (1 + Q) * (1 + P) * (1 - Q) = 1 + Q * P := by
  have h1 : (1 - P) * (1 + Q) = 1 + Q - P := by
    simp only [sub_mul, mul_add, one_mul, mul_one, hPQ]; abel
  have h2 : (1 + P) * (1 - Q) = 1 - Q + P := by
    simp only [add_mul, mul_sub, one_mul, mul_one, hPQ]; abel
  rw [h1, mul_assoc, h2]
  have h3 : (1 + Q - P) * (1 - Q + P) = 1 + Q * P := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hPP, hQQ, hPQ]
    abel
  exact h3


theorem dot_i0_iL : (Pi.single (iL hn) (1 : k) : Fin n → k) ⬝ᵥ Pi.single (i0 hn) (1 : k) = 0 := by
  simp [dotProduct_single, (i0_ne_iL hn).symm]

theorem rowMat_mul (β β' : Fin n → k) (hβ : β (i0 hn) = 0) :
    rowMat hn β * rowMat hn β' = rowMat hn (β + β') := by
  simp only [rowMat, add_mul, mul_add, one_mul, mul_one, vecMulVec_mul_vecMulVec]
  simp [dotProduct_single, hβ]
  rw [vecMulVec_add, add_assoc]

theorem colMat_mul (v v' : Fin n → k) (hv' : v' (iL hn) = 0) :
    colMat hn v * colMat hn v' = colMat hn (v + v') := by
  simp only [colMat, add_mul, mul_add, one_mul, mul_one, vecMulVec_mul_vecMulVec]
  simp [single_dotProduct, hv']
  rw [add_vecMulVec, add_assoc]

theorem rowMat_zero : rowMat hn (0 : Fin n → k) = 1 := by simp [rowMat]

theorem colMat_zero : colMat hn (0 : Fin n → k) = 1 := by simp [colMat]

theorem rowElt_mul (β β' : Fin n → k) (hβ : β (i0 hn) = 0) (hβ' : β' (i0 hn) = 0) :
    rowElt hn β hβ * rowElt hn β' hβ' = rowElt hn (β + β') (by simp [hβ, hβ']) :=
  Subtype.ext (rowMat_mul hn β β' hβ)

theorem colElt_mul (v v' : Fin n → k) (hv : v (iL hn) = 0) (hv' : v' (iL hn) = 0) :
    colElt hn v hv * colElt hn v' hv' = colElt hn (v + v') (by simp [hv, hv']) :=
  Subtype.ext (colMat_mul hn v v' hv')

theorem rowElt_zero : rowElt hn (0 : Fin n → k) (by simp) = 1 :=
  Subtype.ext (rowMat_zero hn)

theorem colElt_zero : colElt hn (0 : Fin n → k) (by simp) = 1 :=
  Subtype.ext (colMat_zero hn)

theorem rowElt_inv (β : Fin n → k) (hβ : β (i0 hn) = 0) :
    (rowElt hn β hβ)⁻¹ = rowElt hn (-β) (by simp [hβ]) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show rowMat hn β * rowMat hn (-β) = 1
  rw [rowMat_mul hn β (-β) hβ, add_neg_cancel, rowMat_zero]

theorem colElt_inv (v : Fin n → k) (hv : v (iL hn) = 0) :
    (colElt hn v hv)⁻¹ = colElt hn (-v) (by simp [hv]) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show colMat hn v * colMat hn (-v) = 1
  rw [colMat_mul hn v (-v) (by simp [hv]), add_neg_cancel, colMat_zero]

theorem single_iL_apply_i0 : (Pi.single (iL hn) (1 : k) : Fin n → k) (i0 hn) = 0 := by
  simp [i0_ne_iL hn]

theorem comm_mat (β v : Fin n → k) (hβ : β (i0 hn) = 0) (hv : v (iL hn) = 0) :
    colMat hn (-v) * rowMat hn β * colMat hn v * rowMat hn (-β) =
      rowMat hn ((β ⬝ᵥ v) • Pi.single (iL hn) (1 : k)) := by
  set P : Matrix (Fin n) (Fin n) k := vecMulVec v (Pi.single (iL hn) (1 : k)) with hP
  set Q : Matrix (Fin n) (Fin n) k := vecMulVec (Pi.single (i0 hn) (1 : k)) β with hQ
  have e1 : colMat hn (-v) = 1 - P := by
    simp [colMat, neg_vecMulVec, sub_eq_add_neg, hP]
  have e2 : colMat hn v = 1 + P := rfl
  have e3 : rowMat hn β = 1 + Q := rfl
  have e4 : rowMat hn (-β) = 1 - Q := by
    simp [rowMat, vecMulVec_neg, sub_eq_add_neg, hQ]
  have hPP : P * P = 0 := by
    rw [hP, vecMulVec_mul_vecMulVec]
    simp [single_dotProduct, hv]
  have hQQ : Q * Q = 0 := by
    rw [hQ, vecMulVec_mul_vecMulVec]
    simp [dotProduct_single, hβ]
  have hPQ : P * Q = 0 := by
    rw [hP, hQ, vecMulVec_mul_vecMulVec, dot_i0_iL hn]
    simp
  have hQP : Q * P = vecMulVec (Pi.single (i0 hn) (1 : k))
      ((β ⬝ᵥ v) • Pi.single (iL hn) (1 : k)) := by
    rw [hP, hQ, vecMulVec_mul_vecMulVec]
  rw [e1, e2, e3, e4, abstract_comm P Q hPP hQQ hPQ, hQP]
  rfl

theorem comm_elt (β v : Fin n → k) (hβ : β (i0 hn) = 0) (hv : v (iL hn) = 0) :
    ⁅(colElt hn v hv)⁻¹, rowElt hn β hβ⁆ =
      rowElt hn ((β ⬝ᵥ v) • (Pi.single (iL hn) (1 : k) : Fin n → k))
        (by simp [single_iL_apply_i0 hn]) := by
  apply Subtype.ext
  rw [commutatorElement_def, inv_inv, rowElt_inv, colElt_inv]
  show colMat hn (-v) * rowMat hn β * colMat hn v * rowMat hn (-β) = _
  exact comm_mat hn β v hβ hv

@[expose] def zElt (c : k) : SL (Fin n) k :=
  rowElt hn (c • (Pi.single (iL hn) (1 : k) : Fin n → k)) (by simp [single_iL_apply_i0 hn])

theorem zElt_mul (c c' : k) : zElt hn c * zElt hn c' = zElt hn (c + c') := by
  apply Subtype.ext
  show rowMat hn (c • (Pi.single (iL hn) (1 : k) : Fin n → k)) *
      rowMat hn (c' • (Pi.single (iL hn) (1 : k) : Fin n → k)) =
    rowMat hn ((c + c') • (Pi.single (iL hn) (1 : k) : Fin n → k))
  rw [rowMat_mul hn _ _ (by simp [single_iL_apply_i0 hn]), add_smul]

theorem zElt_zero : zElt hn (0 : k) = 1 := by
  apply Subtype.ext
  show rowMat hn ((0 : k) • (Pi.single (iL hn) (1 : k) : Fin n → k)) = 1
  rw [zero_smul, rowMat_zero]

theorem zElt_inv (c : k) : (zElt hn c)⁻¹ = zElt hn (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [zElt_mul, add_neg_cancel, zElt_zero]

@[expose] def rowSub : Subgroup (SL (Fin n) k) where
  carrier := {g | ∃ (β : Fin n → k) (hβ : β (i0 hn) = 0), g = rowElt hn β hβ}
  mul_mem' := by
    rintro _ _ ⟨β, hβ, rfl⟩ ⟨β', hβ', rfl⟩
    exact ⟨β + β', by simp [hβ, hβ'], rowElt_mul hn β β' hβ hβ'⟩
  one_mem' := ⟨0, by simp, (rowElt_zero hn).symm⟩
  inv_mem' := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨-β, by simp [hβ], rowElt_inv hn β hβ⟩

@[expose] def zSub : Subgroup (SL (Fin n) k) where
  carrier := {g | ∃ c : k, g = zElt hn c}
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    exact ⟨c + c', zElt_mul hn c c'⟩
  one_mem' := ⟨0, (zElt_zero hn).symm⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    exact ⟨-c, zElt_inv hn c⟩

theorem zSub_le_rowSub : zSub hn ≤ (rowSub hn : Subgroup (SL (Fin n) k)) := by
  rintro _ ⟨c, rfl⟩
  exact ⟨_, _, rfl⟩

theorem rowSub_comm : IsMulCommutative (rowSub hn : Subgroup (SL (Fin n) k)) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨_, ⟨β, hβ, rfl⟩⟩ := a
  obtain ⟨_, ⟨β', hβ', rfl⟩⟩ := b
  apply Subtype.ext
  show rowElt hn β hβ * rowElt hn β' hβ' = rowElt hn β' hβ' * rowElt hn β hβ
  rw [rowElt_mul, rowElt_mul]
  congr 1
  exact add_comm _ _

theorem rowElt_pow (β : Fin n → k) (hβ : β (i0 hn) = 0) (m : ℕ) :
    rowElt hn β hβ ^ m = rowElt hn (m • β) (by simp [hβ]) := by
  induction m with
  | zero =>
    simp only [pow_zero, zero_smul]
    exact (rowElt_zero hn).symm
  | succ m ih =>
    rw [pow_succ, ih, rowElt_mul hn _ _ (by simp [hβ]) hβ]
    congr 1
    rw [succ_nsmul]

theorem rowSub_isPGroup {r : ℕ} [hr : Fact r.Prime] [CharP k r] :
    IsPGroup r (rowSub hn : Subgroup (SL (Fin n) k)) := by
  refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
  obtain ⟨_, ⟨β, hβ, rfl⟩⟩ := g
  have h1 : (⟨rowElt hn β hβ, β, hβ, rfl⟩ : (rowSub hn : Subgroup (SL (Fin n) k))) ^ r = 1 := by
    apply Subtype.ext
    show rowElt hn β hβ ^ r = 1
    rw [rowElt_pow]
    have : r • β = 0 := by
      ext j
      simp [nsmul_eq_mul, CharP.cast_eq_zero]
    simp only [this]
    exact rowElt_zero hn
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.dvd_prime hr.out).mp h2 with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

abbrev Mid : Type := {j : Fin n // j ≠ i0 hn ∧ j ≠ iL hn}

@[expose] def extZero (v : Mid hn → k) : Fin n → k :=
  fun j => if h : j ≠ i0 hn ∧ j ≠ iL hn then v ⟨j, h⟩ else 0

theorem extZero_iL (v : Mid hn → k) : extZero hn v (iL hn) = 0 := by
  simp [extZero]

theorem extZero_mid (v : Mid hn → k) (j : Mid hn) : extZero hn v j.1 = v j := by
  simp [extZero, j.2]

@[expose] def yElt (v : Mid hn → k) : SL (Fin n) k := colElt hn (extZero hn v) (extZero_iL hn v)

theorem card_mid : Nat.card (Mid hn) = n - 2 := by
  have h1 : Fintype.card (Mid hn) = n - 2 := by
    simp only [Mid]
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter (fun j : Fin n => j ≠ i0 hn ∧ j ≠ iL hn)) =
        ((Finset.univ.erase (i0 hn)).erase (iL hn)) := by
      ext j
      simp [and_comm]
    rw [this, Finset.card_erase_of_mem (by simp [(i0_ne_iL hn).symm]),
      Finset.card_erase_of_mem (by simp), Finset.card_univ, Fintype.card_fin]
    omega
  rw [Nat.card_eq_fintype_card, h1]

end CFSG.SignalizerFunctorTheorem.NonLocal
