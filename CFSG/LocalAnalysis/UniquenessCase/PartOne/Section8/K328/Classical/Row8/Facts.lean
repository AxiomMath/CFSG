module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open Matrix
open CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.RankTwoClassical
open scoped commutatorElement

private abbrev k328r8f_Ix := Fin 3 ⊕ Fin 3 ⊕ Fin 2

private abbrev k328r8f_e (F : Type) [Field F] [Fintype F] [DecidableEq F] (i : Fin 3) : k328r8f_Ix → F := bv F (Sum.inl i)
private abbrev k328r8f_f (F : Type) [Field F] [Fintype F] [DecidableEq F] (i : Fin 3) : k328r8f_Ix → F := bv F (Sum.inr (Sum.inl i))
private abbrev k328r8f_u (F : Type) [Field F] [Fintype F] [DecidableEq F] : k328r8f_Ix → F := bv F (Sum.inr (Sum.inr 0))
private abbrev k328r8f_v (F : Type) [Field F] [Fintype F] [DecidableEq F] : k328r8f_Ix → F := bv F (Sum.inr (Sum.inr 1))

private theorem k328r8f_ofNat_mod2 (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : F) = ((n % 2 : ℕ) : F) := by
  rw [show (OfNat.ofNat n : F) = ((n : ℕ) : F) from rfl]
  exact (CharP.natCast_eq_natCast (R := F) (p := 2) (a := n) (b := n % 2)).mpr
    (Nat.mod_mod n 2).symm

private abbrev k328r8f_QQ (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c : F) : (k328r8f_Ix → F) → F := CFSG.MatrixModel.minusQuadCore 3 F b c

private theorem k328r8f_QQ_expand (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c : F) [CharP F 2] (w : k328r8f_Ix → F) :
    k328r8f_QQ F b c w = w (Sum.inl 0) * w (Sum.inr (Sum.inl 0)) +
      w (Sum.inl 1) * w (Sum.inr (Sum.inl 1)) + w (Sum.inl 2) * w (Sum.inr (Sum.inl 2)) +
      w (Sum.inr (Sum.inr 0)) ^ 2 + b * w (Sum.inr (Sum.inr 0)) * w (Sum.inr (Sum.inr 1)) +
      c * w (Sum.inr (Sum.inr 1)) ^ 2 := by
  simp only [k328r8f_QQ, CFSG.MatrixModel.minusQuadCore, Fin.sum_univ_three]

private def k328r8f_zmat (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) : Matrix k328r8f_Ix k328r8f_Ix F :=
  ofColumns F (Sum.elim ![k328r8f_e F 0 + k328r8f_f F 1, k328r8f_f F 0 + k328r8f_e F 1, k328r8f_e F 2]
    (Sum.elim ![k328r8f_e F 1, k328r8f_e F 0, k328r8f_f F 2] ![α • k328r8f_u F + b⁻¹ • k328r8f_v F, (c / b) • k328r8f_u F + (α + 1) • k328r8f_v F]))

private def k328r8f_tmat (F : Type) [Field F] [Fintype F] [DecidableEq F] (_b _c _α : F) : Matrix k328r8f_Ix k328r8f_Ix F :=
  ofColumns F (Sum.elim ![k328r8f_e F 1, k328r8f_e F 0 + k328r8f_e F 1, k328r8f_e F 2]
    (Sum.elim ![k328r8f_f F 0 + k328r8f_f F 1, k328r8f_f F 0, k328r8f_f F 2] ![k328r8f_u F, k328r8f_v F]))

private def k328r8f_matB (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) : Matrix k328r8f_Ix k328r8f_Ix F :=
  ofColumns F (Sum.elim ![
      k328r8f_e F 0 + k328r8f_e F 1 + k328r8f_f F 0 + k328r8f_f F 1, k328r8f_e F 0 + k328r8f_f F 1, k328r8f_e F 2]
    (Sum.elim ![k328r8f_e F 0, k328r8f_e F 0 + k328r8f_e F 1, k328r8f_f F 2]
      ![(1 + α) • k328r8f_u F + b⁻¹ • k328r8f_v F, (c / b) • k328r8f_u F + α • k328r8f_v F]))

private def k328r8f_matP (F : Type) [Field F] [Fintype F] [DecidableEq F] (b _c α : F) : Matrix k328r8f_Ix k328r8f_Ix F :=
  ofColumns F (Sum.elim ![
      k328r8f_e F 0 + k328r8f_e F 1 + k328r8f_f F 1 + k328r8f_u F, k328r8f_e F 1 + k328r8f_f F 0 + k328r8f_f F 1 + (1 + α) • k328r8f_u F + b⁻¹ • k328r8f_v F, k328r8f_e F 2]
    (Sum.elim ![k328r8f_e F 0 + k328r8f_e F 1 + k328r8f_f F 1 + α • k328r8f_u F + b⁻¹ • k328r8f_v F,
        k328r8f_e F 0 + k328r8f_f F 0 + (1 + α) • k328r8f_u F + b⁻¹ • k328r8f_v F, k328r8f_f F 2]
      ![k328r8f_e F 1 + k328r8f_f F 1,
        b • k328r8f_e F 0 + (b * (1 + α)) • k328r8f_e F 1 + b • k328r8f_f F 0 + (b * α) • k328r8f_f F 1]))

private theorem k328r8f_zmat_iso (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    ∀ x, k328r8f_QQ F b c (k328r8f_zmat F b c α *ᵥ x) = k328r8f_QQ F b c x := by
  intro x
  rw [k328r8f_QQ_expand, k328r8f_QQ_expand]
  simp (config := { decide := true }) only [k328r8f_zmat, ofColumns, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.of_apply, bv,
    Pi.single_apply, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.smul_apply, 
    Matrix.cons_val, 
    ite_true, ite_false]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hK : α ^ 2 + α + c * b⁻¹ ^ 2 - 1 = 0 := by
    linear_combination hα + (c * b⁻¹ ^ 2) * h2
  have hb' : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
  simp only [
    zero_mul, add_zero, zero_add, one_mul]
  linear_combination
    (x (Sum.inr (Sum.inr 0)) ^ 2 + b * x (Sum.inr (Sum.inr 0)) * x (Sum.inr (Sum.inr 1)) +
      c * x (Sum.inr (Sum.inr 1)) ^ 2) * hK +
    (α * x (Sum.inr (Sum.inr 0)) ^ 2 + α * c * x (Sum.inr (Sum.inr 1)) ^ 2 +
      c * x (Sum.inr (Sum.inr 1)) ^ 2) * hb' +
    (x (Sum.inl 0) * x (Sum.inl 1) + α * c * x (Sum.inr (Sum.inr 1)) ^ 2 +
      c * x (Sum.inr (Sum.inr 1)) ^ 2 +
      2 * α * b⁻¹ * x (Sum.inr (Sum.inr 0)) * c * x (Sum.inr (Sum.inr 1)) +
      b⁻¹ * x (Sum.inr (Sum.inr 0)) * c * x (Sum.inr (Sum.inr 1))) * h2

private theorem k328r8f_tmat_iso (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2] :
    ∀ x, k328r8f_QQ F b c (k328r8f_tmat F b c α *ᵥ x) = k328r8f_QQ F b c x := by
  intro x
  rw [k328r8f_QQ_expand, k328r8f_QQ_expand]
  simp (config := { decide := true }) only [k328r8f_tmat, ofColumns, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.of_apply, bv,
    Pi.single_apply, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, 
    Matrix.cons_val, 
    ite_true, ite_false]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (x (Sum.inl 1) * x (Sum.inr (Sum.inl 0))) * h2

private theorem k328r8f_hc (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2] (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    c = b ^ 2 * (α ^ 2 + α + 1) := by
  have h := hα
  rw [div_eq_mul_inv] at h
  have hm : b ^ 2 * (α ^ 2 + α) = b ^ 2 + c := by
    rw [h]; field_simp [hb]
  rw [mul_add, mul_one, hm]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (-(b ^ 2)) * h2

private theorem k328r8f_matB_iso (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    ∀ x, k328r8f_QQ F b c (k328r8f_matB F b c α *ᵥ x) = k328r8f_QQ F b c x := by
  intro x
  rw [k328r8f_QQ_expand, k328r8f_QQ_expand]
  simp (config := { decide := true }) only [k328r8f_matB, ofColumns, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.of_apply, bv,
    Pi.single_apply, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.smul_apply, 
    Matrix.cons_val, 
    ite_true, ite_false]
  rw [k328r8f_hc F b c α hα hb]
  ring_nf
  rw [show b⁻¹ ^ 2 = (b ^ 2)⁻¹ from inv_pow b 2]
  field_simp [hb]
  ring_nf
  simp only [k328r8f_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero, Nat.cast_one]
  ring_nf

private theorem k328r8f_matP_iso (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    ∀ x, k328r8f_QQ F b c (k328r8f_matP F b c α *ᵥ x) = k328r8f_QQ F b c x := by
  intro x
  rw [k328r8f_QQ_expand, k328r8f_QQ_expand]
  simp (config := { decide := true }) only [k328r8f_matP, ofColumns, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.of_apply, bv,
    Pi.single_apply, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.smul_apply, 
    Matrix.cons_val, 
    ite_true, ite_false]
  rw [k328r8f_hc F b c α hα hb]
  ring_nf
  try rw [show b⁻¹ ^ 2 = (b ^ 2)⁻¹ from inv_pow b 2]
  field_simp [hb]
  ring_nf
  simp only [k328r8f_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero, Nat.cast_one]
  ring_nf


private def k328r8f_Prow (F : Type) [Field F] [Fintype F] [DecidableEq F] (b _c α : F) (x : k328r8f_Ix → F) : k328r8f_Ix → F :=
  Sum.elim
    ![(x (Sum.inl 0) + x (Sum.inr (Sum.inl 0)) + x (Sum.inr (Sum.inl 1)) + b * x (Sum.inr (Sum.inr 1))),
      (x (Sum.inl 0) + x (Sum.inl 1) + x (Sum.inr (Sum.inl 0)) + x (Sum.inr (Sum.inr 0)) +
        (b * (1 + α)) * x (Sum.inr (Sum.inr 1))),
      x (Sum.inl 2)]
    (Sum.elim
      ![(x (Sum.inl 1) + x (Sum.inr (Sum.inl 1)) + b * x (Sum.inr (Sum.inr 1))),
        (x (Sum.inl 0) + x (Sum.inl 1) + x (Sum.inr (Sum.inl 0)) + x (Sum.inr (Sum.inr 0)) +
          (b * α) * x (Sum.inr (Sum.inr 1))),
        x (Sum.inr (Sum.inl 2))]
      ![(x (Sum.inl 0) + (1 + α) * (x (Sum.inl 1) + x (Sum.inr (Sum.inl 1))) +
            α * x (Sum.inr (Sum.inl 0))),
        b⁻¹ * (x (Sum.inl 1) + x (Sum.inr (Sum.inl 0)) + x (Sum.inr (Sum.inl 1)))])

private def k328r8f_Brow (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) (x : k328r8f_Ix → F) : k328r8f_Ix → F :=
  Sum.elim
    ![(x (Sum.inl 0) + x (Sum.inl 1) + x (Sum.inr (Sum.inl 0)) + x (Sum.inr (Sum.inl 1))),
      (x (Sum.inl 0) + x (Sum.inr (Sum.inl 1))),
      x (Sum.inl 2)]
    (Sum.elim
      ![(x (Sum.inl 0)),
        (x (Sum.inl 0) + x (Sum.inl 1)),
        x (Sum.inr (Sum.inl 2))]
      ![((1 + α) * x (Sum.inr (Sum.inr 0)) + (c / b) * x (Sum.inr (Sum.inr 1))),
        b⁻¹ * x (Sum.inr (Sum.inr 0)) + α * x (Sum.inr (Sum.inr 1))])

private theorem k328r8f_matP_row (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) (x : k328r8f_Ix → F) :
    k328r8f_matP F b c α *ᵥ x = k328r8f_Prow F b c α x := by
  funext r
  fin_cases r <;>
    simp [k328r8f_matP, k328r8f_Prow, ofColumns, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.of_apply, bv,
      Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.smul_apply, 
      Matrix.cons_val, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
  all_goals ring

private theorem k328r8f_matB_row (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) (x : k328r8f_Ix → F) :
    k328r8f_matB F b c α *ᵥ x = k328r8f_Brow F b c α x := by
  funext r
  fin_cases r <;>
    simp [k328r8f_matB, k328r8f_Brow, ofColumns, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.of_apply, bv,
      Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.smul_apply, 
      Matrix.cons_val, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
  all_goals ring

private theorem k328r8f_Prow_triple (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2] (hb : b ≠ 0) (x : k328r8f_Ix → F) :
    k328r8f_Prow F b c α (k328r8f_Prow F b c α (k328r8f_Prow F b c α x)) = x := by
  funext r
  fin_cases r <;> simp [k328r8f_Prow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
  all_goals (
    try rw [show b⁻¹ ^ 2 = (b ^ 2)⁻¹ from inv_pow b 2]
    field_simp [hb]
    ring_nf
    simp only [k328r8f_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero, Nat.cast_one]
    ring_nf)

private theorem k328r8f_Brow_triple (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) (x : k328r8f_Ix → F) :
    k328r8f_Brow F b c α (k328r8f_Brow F b c α (k328r8f_Brow F b c α x)) = x := by
  funext r
  fin_cases r <;> simp [k328r8f_Brow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
  all_goals (
    try rw [k328r8f_hc F b c α hα hb]
    try rw [show b⁻¹ ^ 2 = (b ^ 2)⁻¹ from inv_pow b 2]
    try field_simp [hb]
    try ring_nf
    try simp only [k328r8f_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero, Nat.cast_one]
    try ring_nf)

private theorem k328r8f_matP_mulVec_inj (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2] (hb : b ≠ 0) :
    Function.Injective fun x : k328r8f_Ix → F => k328r8f_matP F b c α *ᵥ x := by
  have hrow := k328r8f_matP_row F b c α
  have htriple := k328r8f_Prow_triple F b c α hb
  have h3 : ∀ y, k328r8f_matP F b c α *ᵥ (k328r8f_matP F b c α *ᵥ
      (k328r8f_matP F b c α *ᵥ y)) = y := by
    intro y; simp only [hrow]; exact htriple y
  intro x y hxy
  have hxy' : k328r8f_matP F b c α *ᵥ x = k328r8f_matP F b c α *ᵥ y := hxy
  calc x = k328r8f_matP F b c α *ᵥ (k328r8f_matP F b c α *ᵥ
        (k328r8f_matP F b c α *ᵥ x)) := (h3 x).symm
    _ = k328r8f_matP F b c α *ᵥ (k328r8f_matP F b c α *ᵥ
        (k328r8f_matP F b c α *ᵥ y)) := by rw [hxy']
    _ = y := h3 y

private theorem k328r8f_matB_mulVec_inj (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    Function.Injective fun x : k328r8f_Ix → F => k328r8f_matB F b c α *ᵥ x := by
  have hrow := k328r8f_matB_row F b c α
  have htriple := k328r8f_Brow_triple F b c α hα hb
  have h3 : ∀ y, k328r8f_matB F b c α *ᵥ (k328r8f_matB F b c α *ᵥ
      (k328r8f_matB F b c α *ᵥ y)) = y := by
    intro y; simp only [hrow]; exact htriple y
  intro x y hxy
  have hxy' : k328r8f_matB F b c α *ᵥ x = k328r8f_matB F b c α *ᵥ y := hxy
  calc x = k328r8f_matB F b c α *ᵥ (k328r8f_matB F b c α *ᵥ
        (k328r8f_matB F b c α *ᵥ x)) := (h3 x).symm
    _ = k328r8f_matB F b c α *ᵥ (k328r8f_matB F b c α *ᵥ
        (k328r8f_matB F b c α *ᵥ y)) := by rw [hxy']
    _ = y := h3 y

private noncomputable def k328r8f_PGL (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2] (hb : b ≠ 0) : GL k328r8f_Ix F :=
  (Matrix.mulVec_injective_iff_isUnit.mp (k328r8f_matP_mulVec_inj F b c α hb)).unit

private noncomputable def k328r8f_BGL (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) : GL k328r8f_Ix F :=
  (Matrix.mulVec_injective_iff_isUnit.mp (k328r8f_matB_mulVec_inj F b c α hα hb)).unit

private theorem k328r8f_PGL_coe (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2] (hb : b ≠ 0) :
    ((k328r8f_PGL F b c α hb : GL k328r8f_Ix F) : Matrix k328r8f_Ix k328r8f_Ix F) = k328r8f_matP F b c α :=
  IsUnit.unit_spec _

private theorem k328r8f_BGL_coe (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    ((k328r8f_BGL F b c α hα hb : GL k328r8f_Ix F) : Matrix k328r8f_Ix k328r8f_Ix F) = k328r8f_matB F b c α :=
  IsUnit.unit_spec _

private theorem k328r8f_mulVec_id_eq_one (F : Type) [Field F] [Fintype F] [DecidableEq F] {M : Matrix k328r8f_Ix k328r8f_Ix F} (h : ∀ x, M *ᵥ x = x) : M = 1 := by
  ext r k
  have hh := congrFun (h (Pi.single k 1)) r
  rw [Matrix.mulVec_single_one] at hh
  simpa [Matrix.one_apply, Pi.single_apply] using hh

private theorem k328r8f_PGL_cube (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2] (hb : b ≠ 0) :
    k328r8f_PGL F b c α hb ^ 3 = 1 := by
  apply Units.ext
  show ((k328r8f_PGL F b c α hb : GL k328r8f_Ix F) : Matrix k328r8f_Ix k328r8f_Ix F) ^ 3 = 1
  rw [k328r8f_PGL_coe]
  apply k328r8f_mulVec_id_eq_one
  intro x
  have hrow := k328r8f_matP_row F b c α
  have htriple := k328r8f_Prow_triple F b c α hb
  have : k328r8f_matP F b c α *ᵥ (k328r8f_matP F b c α *ᵥ
      (k328r8f_matP F b c α *ᵥ x)) = x := by simp only [hrow]; exact htriple x
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc, Matrix.mulVec_mulVec,
    Matrix.one_mulVec] using this

private theorem k328r8f_BGL_cube (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    k328r8f_BGL F b c α hα hb ^ 3 = 1 := by
  apply Units.ext
  show ((k328r8f_BGL F b c α hα hb : GL k328r8f_Ix F) : Matrix k328r8f_Ix k328r8f_Ix F) ^ 3 = 1
  rw [k328r8f_BGL_coe]
  apply k328r8f_mulVec_id_eq_one
  intro x
  have hrow := k328r8f_matB_row F b c α
  have htriple := k328r8f_Brow_triple F b c α hα hb
  have : k328r8f_matB F b c α *ᵥ (k328r8f_matB F b c α *ᵥ
      (k328r8f_matB F b c α *ᵥ x)) = x := by simp only [hrow]; exact htriple x
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc, Matrix.mulVec_mulVec,
    Matrix.one_mulVec] using this


private def k328r8f_Trow (F : Type) [Field F] [Fintype F] [DecidableEq F] (_b _c _α : F) (x : k328r8f_Ix → F) : k328r8f_Ix → F :=
  Sum.elim
    ![(x (Sum.inl 1)), (x (Sum.inl 0) + x (Sum.inl 1)), x (Sum.inl 2)]
    (Sum.elim
      ![(x (Sum.inr (Sum.inl 0)) + x (Sum.inr (Sum.inl 1))), x (Sum.inr (Sum.inl 0)),
        x (Sum.inr (Sum.inl 2))]
      ![x (Sum.inr (Sum.inr 0)), x (Sum.inr (Sum.inr 1))])

private def k328r8f_zrow (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) (x : k328r8f_Ix → F) : k328r8f_Ix → F :=
  Sum.elim
    ![(x (Sum.inl 0) + x (Sum.inr (Sum.inl 1))), (x (Sum.inl 1) + x (Sum.inr (Sum.inl 0))),
      x (Sum.inl 2)]
    (Sum.elim
      ![x (Sum.inl 1), x (Sum.inl 0), x (Sum.inr (Sum.inl 2))]
      ![(α * x (Sum.inr (Sum.inr 0)) + (c / b) * x (Sum.inr (Sum.inr 1))),
        b⁻¹ * x (Sum.inr (Sum.inr 0)) + (α + 1) * x (Sum.inr (Sum.inr 1))])

private theorem k328r8f_matT_row (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) (x : k328r8f_Ix → F) :
    k328r8f_tmat F b c α *ᵥ x = k328r8f_Trow F b c α x := by
  funext r
  fin_cases r <;>
    simp [k328r8f_tmat, k328r8f_Trow, ofColumns, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.of_apply, bv,
      Sum.elim_inl, Sum.elim_inr, Pi.add_apply, 
      Matrix.cons_val, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]

private theorem k328r8f_matZ_row (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) (x : k328r8f_Ix → F) :
    k328r8f_zmat F b c α *ᵥ x = k328r8f_zrow F b c α x := by
  funext r
  fin_cases r <;>
    simp [k328r8f_zmat, k328r8f_zrow, ofColumns, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.of_apply, bv,
      Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.smul_apply, 
      Matrix.cons_val, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]

private theorem k328r8f_ext_mulVec (F : Type) [Field F] [Fintype F] [DecidableEq F] {M N : Matrix k328r8f_Ix k328r8f_Ix F} (h : ∀ x, M *ᵥ x = N *ᵥ x) :
    M = N := by
  ext r k
  have hh := congrFun (h (Pi.single k 1)) r
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hh
  exact hh

private theorem k328r8f_Trow_triple (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2] (x : k328r8f_Ix → F) :
    k328r8f_Trow F b c α (k328r8f_Trow F b c α (k328r8f_Trow F b c α x)) = x := by
  funext r
  fin_cases r <;> simp [k328r8f_Trow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
  all_goals (
    ring_nf
    simp only [k328r8f_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero, Nat.cast_one]
    ring_nf)

private theorem k328r8f_charP (F : Type) [Field F] [Fintype F] [DecidableEq F] (hF : Fintype.card F = 8) : CharP F 2 :=
  charP_of_card_eq_prime_pow (p := 2) (f := 3) (by rw [hF]; norm_num)

private theorem k328r8f_quadMinus_eq_QQ (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c : F) :
    ⇑(quadMinus 4 F b c) = k328r8f_QQ F b c := by
  funext k328r8f_v
  rw [quadMinus_apply]
  simp only [k328r8f_QQ, CFSG.MatrixModel.minusQuadCore]

private theorem k328r8f_zrow_triple (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) (x : k328r8f_Ix → F) :
    k328r8f_zrow F b c α (k328r8f_zrow F b c α (k328r8f_zrow F b c α x)) = x := by
  funext r
  fin_cases r <;> simp [k328r8f_zrow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
  all_goals (
    try rw [k328r8f_hc F b c α hα hb]
    try rw [show b⁻¹ ^ 2 = (b ^ 2)⁻¹ from inv_pow b 2]
    try field_simp [hb]
    try ring_nf
    try simp only [k328r8f_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero, Nat.cast_one]
    try ring_nf)

private theorem k328r8f_zmat_cube (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    k328r8f_zmat F b c α ^ 3 = 1 := by
  apply k328r8f_mulVec_id_eq_one
  intro x
  have hrow := k328r8f_matZ_row F b c α
  have htriple := k328r8f_zrow_triple F b c α hα hb
  have : k328r8f_zmat F b c α *ᵥ (k328r8f_zmat F b c α *ᵥ
      (k328r8f_zmat F b c α *ᵥ x)) = x := by simp only [hrow]; exact htriple x
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc, Matrix.mulVec_mulVec,
    Matrix.one_mulVec] using this

private theorem k328r8f_tmat_cube (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2] :
    k328r8f_tmat F b c α ^ 3 = 1 := by
  apply k328r8f_mulVec_id_eq_one
  intro x
  have hrow := k328r8f_matT_row F b c α
  have htriple := k328r8f_Trow_triple F b c α
  have : k328r8f_tmat F b c α *ᵥ (k328r8f_tmat F b c α *ᵥ
      (k328r8f_tmat F b c α *ᵥ x)) = x := by simp only [hrow]; exact htriple x
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc, Matrix.mulVec_mulVec,
    Matrix.one_mulVec] using this

private theorem k328r8f_zmat_ne_one (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) : k328r8f_zmat F b c α ≠ 1 := by
  intro h
  have hval : (k328r8f_zmat F b c α *ᵥ bv F (Sum.inl 0)) (Sum.inr (Sum.inl 1)) = 1 := by
    rw [k328r8f_matZ_row]
    simp [k328r8f_zrow, bv]
  rw [h, Matrix.one_mulVec] at hval
  simp [bv] at hval

private theorem k328r8f_tmat_ne_one (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) : k328r8f_tmat F b c α ≠ 1 := by
  intro h
  have hval : (k328r8f_tmat F b c α *ᵥ bv F (Sum.inl 0)) (Sum.inl 1) = 1 := by
    rw [k328r8f_matT_row]
    simp [k328r8f_Trow, bv]
  rw [h, Matrix.one_mulVec] at hval
  simp [bv] at hval

private theorem k328r8f_orderOf_eq_three (F : Type) [Field F] [Fintype F] [DecidableEq F] {M : GL k328r8f_Ix F} (h3 : M ^ 3 = 1) (h1 : M ≠ 1) :
    orderOf M = 3 :=
  orderOf_eq_prime h3 h1

private theorem k328r8f_ZT_comm (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (_hα : α ^ 2 + α = 1 + c / b ^ 2) (_hb : b ≠ 0) :
    k328r8f_zmat F b c α * k328r8f_tmat F b c α =
      k328r8f_tmat F b c α * k328r8f_zmat F b c α := by
  apply k328r8f_ext_mulVec
  intro x
  simp only [← Matrix.mulVec_mulVec, k328r8f_matZ_row, k328r8f_matT_row]
  funext r
  fin_cases r <;>
    simp [k328r8f_zrow, k328r8f_Trow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
  all_goals (
    try rw [k328r8f_hc F b c α _hα _hb]
    try rw [show b⁻¹ ^ 2 = (b ^ 2)⁻¹ from inv_pow b 2]
    try field_simp [_hb]
    try ring_nf
    try simp only [k328r8f_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero, Nat.cast_one]
    try ring_nf)

private theorem k328r8f_ZB_comm (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    k328r8f_zmat F b c α * k328r8f_matB F b c α =
      k328r8f_matB F b c α * k328r8f_zmat F b c α := by
  apply k328r8f_ext_mulVec
  intro x
  simp only [← Matrix.mulVec_mulVec, k328r8f_matZ_row, k328r8f_matB_row]
  funext r
  fin_cases r <;>
    simp [k328r8f_zrow, k328r8f_Brow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
  all_goals (
    try rw [k328r8f_hc F b c α hα hb]
    try rw [show b⁻¹ ^ 2 = (b ^ 2)⁻¹ from inv_pow b 2]
    try field_simp [hb]
    try ring_nf
    try simp only [k328r8f_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero]
    try ring_nf)

private theorem k328r8f_ZP_comm (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    k328r8f_zmat F b c α * k328r8f_matP F b c α =
      k328r8f_matP F b c α * k328r8f_zmat F b c α := by
  apply k328r8f_ext_mulVec
  intro x
  simp only [← Matrix.mulVec_mulVec, k328r8f_matZ_row, k328r8f_matP_row]
  funext r
  fin_cases r <;>
    simp [k328r8f_zrow, k328r8f_Prow, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
  all_goals (
    try rw [k328r8f_hc F b c α hα hb]
    try rw [show b⁻¹ ^ 2 = (b ^ 2)⁻¹ from inv_pow b 2]
    try field_simp [hb]
    try ring_nf
    try simp only [k328r8f_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero, Nat.cast_one]
    try ring_nf)

private theorem k328r8f_TP_eq (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    k328r8f_tmat F b c α * k328r8f_matP F b c α =
      k328r8f_zmat F b c α * k328r8f_matP F b c α * k328r8f_tmat F b c α := by
  apply k328r8f_ext_mulVec
  intro x
  simp only [← Matrix.mulVec_mulVec, k328r8f_matT_row, k328r8f_matP_row, k328r8f_matZ_row]
  funext r
  fin_cases r <;>
    simp [k328r8f_Trow, k328r8f_Prow, k328r8f_zrow, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val]
  all_goals (
    try rw [k328r8f_hc F b c α hα hb]
    try rw [show b⁻¹ ^ 2 = (b ^ 2)⁻¹ from inv_pow b 2]
    try field_simp [hb]
    try ring_nf
    try simp only [k328r8f_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero, Nat.cast_one]
    try ring_nf)

private theorem k328r8f_BP_eq (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) [CharP F 2]
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (hb : b ≠ 0) :
    k328r8f_matB F b c α * k328r8f_matP F b c α =
      k328r8f_tmat F b c α * k328r8f_matP F b c α * k328r8f_matB F b c α := by
  apply k328r8f_ext_mulVec
  intro x
  simp only [← Matrix.mulVec_mulVec, k328r8f_matB_row, k328r8f_matP_row, k328r8f_matT_row]
  funext r
  fin_cases r <;>
    simp [k328r8f_Brow, k328r8f_Prow, k328r8f_Trow, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val]
  all_goals (
    try rw [k328r8f_hc F b c α hα hb]
    try rw [show b⁻¹ ^ 2 = (b ^ 2)⁻¹ from inv_pow b 2]
    try field_simp [hb]
    try ring_nf
    try simp only [k328r8f_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero, Nat.cast_one]
    try ring_nf)

private theorem k328r8f_mem_statedOmega_of_iso_of_cube (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {M : GL k328r8f_Ix F}
    (hiso : ∀ k328r8f_v, k328r8f_QQ F b c ((M : Matrix k328r8f_Ix k328r8f_Ix F) *ᵥ k328r8f_v) = k328r8f_QQ F b c k328r8f_v)
    (h3 : M ^ 3 = 1) :
    M ∈ StatedOmega (StatedQuadMinus 4 F b c) := by
  have : CharP F 2 := k328r8f_charP F hF
  have hQ : (quadMinus 4 F b c).polarBilin.Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite (n := 4) F hbc
  have hT := exists_totallySingular_quadMinus (n := 4) (by norm_num) F b c
  have hM2 : M ^ 2 ∈ StatedOmega ⇑(quadMinus 4 F b c) :=
    sq_mem_statedOmega (quadMinus 4 F b c) hQ hT (fun k328r8f_v => by
      rw [k328r8f_quadMinus_eq_QQ]
      exact hiso k328r8f_v)
  rw [coe_quadMinus] at hM2
  have hsq : (M ^ 2) ^ 2 = M := by
    rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 from rfl, pow_succ, h3, one_mul]
  rw [← hsq]
  exact (StatedOmega (StatedQuadMinus 4 F b c)).pow_mem hM2 2

private theorem k328r8f_row8_facts (F : Type) [Field F] [Fintype F] [DecidableEq F] (hF : Fintype.card F = 8) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (α : F) (hα : α ^ 2 + α = 1 + c / b ^ 2) :
    ∀ z₀ t₀ : GL k328r8f_Ix F,
    (z₀ : Matrix k328r8f_Ix k328r8f_Ix F) = ofColumns F (Sum.elim ![k328r8f_e F 0 + k328r8f_f F 1, k328r8f_f F 0 + k328r8f_e F 1, k328r8f_e F 2]
      (Sum.elim ![k328r8f_e F 1, k328r8f_e F 0, k328r8f_f F 2]
        ![α • k328r8f_u F + b⁻¹ • k328r8f_v F, (c / b) • k328r8f_u F + (α + 1) • k328r8f_v F])) →
    (t₀ : Matrix k328r8f_Ix k328r8f_Ix F) = ofColumns F (Sum.elim ![k328r8f_e F 1, k328r8f_e F 0 + k328r8f_e F 1, k328r8f_e F 2]
      (Sum.elim ![k328r8f_f F 0 + k328r8f_f F 1, k328r8f_f F 0, k328r8f_f F 2] ![k328r8f_u F, k328r8f_v F])) →
    FactsLeaf (StatedOmega (StatedQuadMinus 4 F b c)) z₀ t₀ := by
  intro z₀ t₀ hz ht
  have : CharP F 2 := k328r8f_charP F hF
  have hb : b ≠ 0 := by
    intro hb0
    have hrc : ringChar F = 2 := ringChar.eq F 2
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hrc c
    have h := hbc s
    rw [hb0, zero_mul, add_zero, pow_two, hs] at h
    exact h (CharTwo.add_self_eq_zero (s * s))
  have hz' : (z₀ : Matrix k328r8f_Ix k328r8f_Ix F) = k328r8f_zmat F b c α := hz
  have ht' : (t₀ : Matrix k328r8f_Ix k328r8f_Ix F) = k328r8f_tmat F b c α := ht
  let P : GL k328r8f_Ix F := k328r8f_PGL F b c α hb
  let B : GL k328r8f_Ix F := k328r8f_BGL F b c α hα hb
  have hPc : (P : Matrix k328r8f_Ix k328r8f_Ix F) = k328r8f_matP F b c α := k328r8f_PGL_coe F b c α hb
  have hBc : (B : Matrix k328r8f_Ix k328r8f_Ix F) = k328r8f_matB F b c α := k328r8f_BGL_coe F b c α hα hb
  have hz3 : z₀ ^ 3 = 1 := by
    apply Units.ext
    show ((z₀ : GL k328r8f_Ix F) : Matrix k328r8f_Ix k328r8f_Ix F) ^ 3 = 1
    rw [hz']
    exact k328r8f_zmat_cube F b c α hα hb
  have ht3 : t₀ ^ 3 = 1 := by
    apply Units.ext
    show ((t₀ : GL k328r8f_Ix F) : Matrix k328r8f_Ix k328r8f_Ix F) ^ 3 = 1
    rw [ht']
    exact k328r8f_tmat_cube F b c α
  have hP3 : P ^ 3 = 1 := k328r8f_PGL_cube F b c α hb
  have hB3 : B ^ 3 = 1 := k328r8f_BGL_cube F b c α hα hb
  have hz1 : z₀ ≠ 1 := by
    intro h
    have h' : k328r8f_zmat F b c α = 1 := by rw [← hz', h]; rfl
    exact k328r8f_zmat_ne_one F b c α h'
  have ht1 : t₀ ≠ 1 := by
    intro h
    have h' : k328r8f_tmat F b c α = 1 := by rw [← ht', h]; rfl
    exact k328r8f_tmat_ne_one F b c α h'
  have hoz : orderOf z₀ = 3 := k328r8f_orderOf_eq_three F hz3 hz1
  have hot : orderOf t₀ = 3 := k328r8f_orderOf_eq_three F ht3 ht1
  have hz_iso : ∀ k328r8f_v, k328r8f_QQ F b c ((z₀ : Matrix k328r8f_Ix k328r8f_Ix F) *ᵥ k328r8f_v) = k328r8f_QQ F b c k328r8f_v := by
    intro k328r8f_v; rw [hz']; exact k328r8f_zmat_iso F b c α hα hb k328r8f_v
  have ht_iso : ∀ k328r8f_v, k328r8f_QQ F b c ((t₀ : Matrix k328r8f_Ix k328r8f_Ix F) *ᵥ k328r8f_v) = k328r8f_QQ F b c k328r8f_v := by
    intro k328r8f_v; rw [ht']; exact k328r8f_tmat_iso F b c α k328r8f_v
  have hB_iso : ∀ k328r8f_v, k328r8f_QQ F b c ((B : Matrix k328r8f_Ix k328r8f_Ix F) *ᵥ k328r8f_v) = k328r8f_QQ F b c k328r8f_v := by
    intro k328r8f_v; rw [hBc]; exact k328r8f_matB_iso F b c α hα hb k328r8f_v
  have hP_iso : ∀ k328r8f_v, k328r8f_QQ F b c ((P : Matrix k328r8f_Ix k328r8f_Ix F) *ᵥ k328r8f_v) = k328r8f_QQ F b c k328r8f_v := by
    intro k328r8f_v; rw [hPc]; exact k328r8f_matP_iso F b c α hα hb k328r8f_v
  have hzH : z₀ ∈ StatedOmega (StatedQuadMinus 4 F b c) :=
    k328r8f_mem_statedOmega_of_iso_of_cube F hF b c hbc hz_iso hz3
  have htH : t₀ ∈ StatedOmega (StatedQuadMinus 4 F b c) :=
    k328r8f_mem_statedOmega_of_iso_of_cube F hF b c hbc ht_iso ht3
  have hBH : B ∈ StatedOmega (StatedQuadMinus 4 F b c) :=
    k328r8f_mem_statedOmega_of_iso_of_cube F hF b c hbc hB_iso hB3
  have hPH : P ∈ StatedOmega (StatedQuadMinus 4 F b c) :=
    k328r8f_mem_statedOmega_of_iso_of_cube F hF b c hbc hP_iso hP3
  have hZT : z₀ * t₀ = t₀ * z₀ := by
    apply Units.ext
    show (z₀ : Matrix k328r8f_Ix k328r8f_Ix F) * (t₀ : Matrix k328r8f_Ix k328r8f_Ix F) =
      (t₀ : Matrix k328r8f_Ix k328r8f_Ix F) * (z₀ : Matrix k328r8f_Ix k328r8f_Ix F)
    rw [hz', ht']
    exact k328r8f_ZT_comm F b c α hα hb
  have hZB : z₀ * B = B * z₀ := by
    apply Units.ext
    show (z₀ : Matrix k328r8f_Ix k328r8f_Ix F) * (B : Matrix k328r8f_Ix k328r8f_Ix F) =
      (B : Matrix k328r8f_Ix k328r8f_Ix F) * (z₀ : Matrix k328r8f_Ix k328r8f_Ix F)
    rw [hz', hBc]
    exact k328r8f_ZB_comm F b c α hα hb
  have hZP : z₀ * P = P * z₀ := by
    apply Units.ext
    show (z₀ : Matrix k328r8f_Ix k328r8f_Ix F) * (P : Matrix k328r8f_Ix k328r8f_Ix F) =
      (P : Matrix k328r8f_Ix k328r8f_Ix F) * (z₀ : Matrix k328r8f_Ix k328r8f_Ix F)
    rw [hz', hPc]
    exact k328r8f_ZP_comm F b c α hα hb
  let C : Subgroup (GL k328r8f_Ix F) :=
    StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {z₀}
  have hT_C : t₀ ∈ C := by
    refine ⟨htH, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hZT)
  have hB_C : B ∈ C := by
    refine ⟨hBH, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hZB)
  have hP_C : P ∈ C := by
    refine ⟨hPH, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hZP)
  have hTP_gl : t₀ * P = z₀ * P * t₀ := by
    apply Units.ext
    show (t₀ : Matrix k328r8f_Ix k328r8f_Ix F) * (P : Matrix k328r8f_Ix k328r8f_Ix F) =
      (z₀ : Matrix k328r8f_Ix k328r8f_Ix F) * (P : Matrix k328r8f_Ix k328r8f_Ix F) * (t₀ : Matrix k328r8f_Ix k328r8f_Ix F)
    rw [ht', hz', hPc]
    exact k328r8f_TP_eq F b c α hα hb
  have hTP : ⁅t₀, P⁆ = z₀ := by
    rw [commutatorElement_def, hTP_gl]
    group
  have hBP_gl : B * P = t₀ * P * B := by
    apply Units.ext
    show (B : Matrix k328r8f_Ix k328r8f_Ix F) * (P : Matrix k328r8f_Ix k328r8f_Ix F) =
      (t₀ : Matrix k328r8f_Ix k328r8f_Ix F) * (P : Matrix k328r8f_Ix k328r8f_Ix F) * (B : Matrix k328r8f_Ix k328r8f_Ix F)
    rw [hBc, ht', hPc]
    exact k328r8f_BP_eq F b c α hα hb
  have hBP : ⁅B, P⁆ = t₀ := by
    rw [commutatorElement_def, hBP_gl]
    group
  have hz_std : z₀ ∈ stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀ := by
    have h := Subgroup.commutator_mem_commutator hT_C hP_C
    rw [hTP] at h
    simpa only [stdComp] using h
  have ht_std : t₀ ∈ stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀ := by
    have h := Subgroup.commutator_mem_commutator hB_C hP_C
    rw [hBP] at h
    simpa only [stdComp] using h
  have htu : (t₀ : Matrix k328r8f_Ix k328r8f_Ix F) *ᵥ bv F (Sum.inr (Sum.inr 0)) =
      bv F (Sum.inr (Sum.inr 0)) := by
    rw [ht', k328r8f_matT_row]
    funext r
    fin_cases r <;> simp [k328r8f_Trow, bv]
  have hzu : (z₀ : Matrix k328r8f_Ix k328r8f_Ix F) *ᵥ bv F (Sum.inr (Sum.inr 0)) =
      α • bv F (Sum.inr (Sum.inr 0)) + b⁻¹ • bv F (Sum.inr (Sum.inr 1)) := by
    rw [hz', k328r8f_matZ_row]
    funext r
    fin_cases r <;> simp [k328r8f_zrow, bv]
  have ht_ne_z : t₀ ≠ z₀ := by
    intro h
    rw [h] at htu
    rw [hzu] at htu
    have hv := congrFun htu (Sum.inr (Sum.inr 1))
    simp [Pi.add_apply, Pi.smul_apply, bv] at hv
    exact hb hv
  have ht_ne_z2 : t₀ ≠ z₀ ^ 2 := by
    intro h
    have hz_eq : z₀ = t₀ ^ 2 := by
      rw [h, ← pow_mul, show (2 * 2 : ℕ) = 3 + 1 from rfl, pow_succ, hz3, one_mul]
    have h2 : (z₀ : Matrix k328r8f_Ix k328r8f_Ix F) *ᵥ bv F (Sum.inr (Sum.inr 0)) =
        bv F (Sum.inr (Sum.inr 0)) := by
      rw [hz_eq]
      show ((t₀ : Matrix k328r8f_Ix k328r8f_Ix F) ^ 2) *ᵥ bv F (Sum.inr (Sum.inr 0)) =
        bv F (Sum.inr (Sum.inr 0))
      rw [pow_two, ← Matrix.mulVec_mulVec, htu, htu]
    rw [hzu] at h2
    have hv := congrFun h2 (Sum.inr (Sum.inr 1))
    simp [Pi.add_apply, Pi.smul_apply, bv] at hv
    exact hb hv
  have ht_notmem : t₀ ∉ Subgroup.zpowers z₀ := by
    intro h
    rw [Subgroup.mem_zpowers_iff] at h
    obtain ⟨k, hk⟩ := h
    have hk' : z₀ ^ (k % (orderOf z₀ : ℤ)) = t₀ := by rw [zpow_mod_orderOf, hk]
    rw [hoz] at hk'
    have hbound : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by
      have hb3 : (((3 : ℕ) : ℤ)) ≠ 0 := by norm_num
      have hb3' : (0 : ℤ) < ((3 : ℕ) : ℤ) := by norm_num
      have h1 := Int.emod_nonneg k hb3
      have h2 := Int.emod_lt_of_pos k hb3'
      omega
    rcases hbound with h0 | h1' | h2'
    · rw [h0] at hk'; simp at hk'; exact ht1 hk'.symm
    · rw [h1'] at hk'; simp at hk'; exact ht_ne_z hk'.symm
    · rw [h2'] at hk'; simp at hk'; exact ht_ne_z2 hk'.symm
  exact ⟨hzH, hz_std, ht_std, hoz, hot, hZT, ht_notmem⟩


theorem row8_facts (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (α : F) (hα : α ^ 2 + α = 1 + c / b ^ 2) :
    let e : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inl i)
    let f : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inr (Sum.inl i))
    let u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 0))
    let v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 1))
    ∀ z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F,
    (z₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 0 + f 1, f 0 + e 1, e 2]
      (Sum.elim ![e 1, e 0, f 2] ![α • u + b⁻¹ • v, (c / b) • u + (α + 1) • v])) →
    (t₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 1, e 0 + e 1, e 2]
      (Sum.elim ![f 0 + f 1, f 0, f 2] ![u, v])) →
    FactsLeaf (StatedOmega (StatedQuadMinus 4 F b c)) z₀ t₀ :=
  k328r8f_row8_facts F hF b c hbc α hα

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
