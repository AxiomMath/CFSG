module

public import CFSG.RankThree.PartOne.MB3.LnSevenReindex

public section

namespace CFSG.RankThree.PartOne.TAIL

open Matrix Subgroup
open CFSG.RankThree.PartOne.MB3 (D2 D2_injective coe_D2 bd2 bd2_mul bd2_det)

@[expose] def sM : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 1; 0, 1, 1]

@[expose] def nM : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem sM_transpose : sM.transpose = sM := by decide +kernel

theorem sM_pow_seven : sM ^ 7 = 1 := by decide +kernel

theorem sM_ne_one : sM ≠ 1 := by decide +kernel

theorem sM_det : sM.det = 1 := by decide +kernel

theorem nM_det : nM.det = 1 := by decide +kernel

theorem nM_mul_sM : nM * sM = sM ^ 2 * nM := by decide +kernel

@[expose] def sSL : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨sM, sM_det⟩

@[expose] def nSL : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨nM, nM_det⟩

theorem coe_sSL : (sSL : Matrix (Fin 3) (Fin 3) (ZMod 2)) = sM := rfl

theorem coe_sSL_pow (i : ℕ) :
    ((sSL ^ i : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      sM ^ i := by
  rw [Matrix.SpecialLinearGroup.coe_pow]
  rfl

theorem orderOf_sSL : orderOf sSL = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  refine orderOf_eq_prime (Subtype.ext ?_) (fun h => sM_ne_one (congrArg Subtype.val h))
  rw [coe_sSL_pow]
  exact sM_pow_seven

theorem nSL_mul_sSL : nSL * sSL = sSL ^ 2 * nSL := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sSL_pow]
  exact nM_mul_sM

theorem nSL_conj_sSL : nSL * sSL * nSL⁻¹ = sSL ^ 2 := by
  rw [nSL_mul_sSL, mul_assoc, mul_inv_cancel, mul_one]

theorem nSL_conj_zpow (i : ℤ) : nSL * sSL ^ i * nSL⁻¹ = sSL ^ (2 * i) := by
  have h : (MulAut.conj nSL) (sSL ^ i) = ((MulAut.conj nSL) sSL) ^ i := map_zpow _ _ _
  rw [MulAut.conj_apply] at h
  rw [h, MulAut.conj_apply, nSL_conj_sSL, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem sSL_zpow_eq_iff {a b : ℤ} : sSL ^ a = sSL ^ b ↔ (a : ZMod 7) = (b : ZMod 7) := by
  rw [zpow_eq_zpow_iff_modEq, orderOf_sSL, ZMod.intCast_eq_intCast_iff]

section Block

variable {κ : Type} [Fintype κ] [DecidableEq κ]

abbrev SLX (κ : Type) [Fintype κ] [DecidableEq κ] : Type :=
  SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)

@[expose] def b1 : SLX κ := D2 (sSL, 1)

@[expose] def b2 : SLX κ := D2 (1, sSL)

@[expose] def x1 : SLX κ := D2 (nSL, 1)

@[expose] def eB (κ : Type) [Fintype κ] [DecidableEq κ] (i j : ℤ) : SLX κ := b1 ^ i * b2 ^ j

theorem eB_eq_D2 (i j : ℤ) : eB κ i j = D2 (sSL ^ i, sSL ^ j) := by
  have h1 : (b1 : SLX κ) ^ i = D2 (sSL ^ i, 1) := by
    rw [b1, ← map_zpow]
    simp
  have h2 : (b2 : SLX κ) ^ j = D2 (1, sSL ^ j) := by
    rw [b2, ← map_zpow]
    simp
  rw [eB, h1, h2, ← map_mul]
  simp

theorem eB_mul (i j i' j' : ℤ) : eB κ i j * eB κ i' j' = eB κ (i + i') (j + j') := by
  simp only [eB_eq_D2, ← map_mul, Prod.mk_mul_mk, zpow_add]

theorem eB_inv (i j : ℤ) : (eB κ i j)⁻¹ = eB κ (-i) (-j) := by
  simp only [eB_eq_D2, ← map_inv, Prod.inv_mk, zpow_neg]

theorem eB_zero : eB κ 0 0 = 1 := by
  rw [eB_eq_D2, zpow_zero]
  exact map_one (D2 (κ := κ))

theorem eB_eq_iff {i j i' j' : ℤ} :
    eB κ i j = eB κ i' j' ↔ (i : ZMod 7) = i' ∧ (j : ZMod 7) = j' := by
  rw [eB_eq_D2, eB_eq_D2, (D2_injective (κ := κ)).eq_iff, Prod.mk.injEq, sSL_zpow_eq_iff,
    sSL_zpow_eq_iff]

theorem eB_pow (i j m : ℤ) : (eB κ i j) ^ m = eB κ (m * i) (m * j) := by
  rw [eB_eq_D2, eB_eq_D2, ← map_zpow]
  congr 1
  refine Prod.ext ?_ ?_
  · show (sSL ^ i) ^ m = sSL ^ (m * i)
    rw [← zpow_mul, mul_comm]
  · show (sSL ^ j) ^ m = sSL ^ (m * j)
    rw [← zpow_mul, mul_comm]

end Block

end CFSG.RankThree.PartOne.TAIL
