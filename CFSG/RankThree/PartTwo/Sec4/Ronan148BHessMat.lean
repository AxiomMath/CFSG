module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix

variable {F : Type*} [Field F] {ω : F}

@[expose] def hessSMat (ω : F) (k : Fin 3) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => 2 / 3 * ω ^ (k.val * i.val + 2 * (k.val * j.val)) - if i = j then 1 else 0

theorem hessPhi_conj_hessT (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) (k : Fin 3) :
    ((hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      hessSMat ω k := by
  rw [Units.val_mul, Units.val_mul, coe_hessPhi, coe_hessPhi_inv, coe_hessT]
  have h1 := one_add_two_mul_ne_zero hω h3
  have h2 := one_add_two_mul_sq_ne_zero hω h3
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessPhiMat, hessPhiInvMat, hessTMat, hessSMat,
      Matrix.diagonal] <;>
    field_simp <;>
    grind

theorem hessPhi_conj_hessS (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) (k : Fin 3) :
    hessPhi hω h3 * (hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) * (hessPhi hω h3)⁻¹ =
      hessT (-k) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hessPhi_conj_hessT hω h3, coe_hessPhi, coe_hessPhi_inv,
    coe_hessT]
  have h1 := one_add_two_mul_ne_zero hω h3
  have h2 := one_add_two_mul_sq_ne_zero hω h3
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessPhiMat, hessPhiInvMat, hessTMat, hessSMat,
      Matrix.diagonal] <;>
    field_simp <;>
    grind

@[expose] def hessZMat (ω : F) : Matrix (Fin 3) (Fin 3) F := fun i j =>
  if i = 0 then (if j = 0 then 1 else 0) else if j = 0 then 0 else
    if i = j then -1 / 2 else -(1 + 2 * ω) / 2

theorem hessZMat_cube (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : F) ≠ 0) :
    hessZMat ω * (hessZMat ω * hessZMat ω) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessZMat, Matrix.one_apply] <;>
    field_simp <;>
    grind

theorem hessZMat_cube' (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : F) ≠ 0) :
    hessZMat ω * hessZMat ω * hessZMat ω = 1 := by
  rw [Matrix.mul_assoc, hessZMat_cube hω h2]

@[expose] def hessZ (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : F) ≠ 0) : GL (Fin 3) F :=
  ⟨hessZMat ω, hessZMat ω * hessZMat ω, hessZMat_cube hω h2, hessZMat_cube' hω h2⟩

theorem coe_hessZ (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : F) ≠ 0) :
    ((hessZ hω h2 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = hessZMat ω :=
  rfl

@[expose] def hessWMat (ω : F) : Matrix (Fin 3) (Fin 3) F := fun i j =>
  if i = 0 then (if j = 0 then (-1 - 2 * ω) / 3 else (2 + ω) / 3) else if j = 0 then (2 + ω) / 3
    else if i = j then (1 + 2 * ω) / 6 else (1 - 4 * ω) / 6

theorem hessPhiMat_mul_hessZMat_mul (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) : hessPhiMat ω * hessZMat ω * hessPhiInvMat ω = hessWMat ω := by
  have h1 := one_add_two_mul_ne_zero hω h3
  have h1' := one_add_two_mul_sq_ne_zero hω h3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessPhiMat, hessPhiInvMat, hessZMat, hessWMat] <;>
    field_simp <;>
    grind

theorem hessZMat_mul_hessWMat_mul (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) : hessZMat ω * hessWMat ω * hessZMat ω = hessPhiMat ω := by
  have h1 := one_add_two_mul_ne_zero hω h3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessPhiMat, hessZMat, hessWMat] <;>
    field_simp <;>
    grind

theorem hessPhi_eq (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    hessPhi hω h3 =
      hessZ hω h2 * (hessPhi hω h3 * hessZ hω h2 * (hessPhi hω h3)⁻¹) * hessZ hω h2 := by
  apply Units.ext
  simp only [Units.val_mul, coe_hessPhi, coe_hessPhi_inv, coe_hessZ]
  rw [hessPhiMat_mul_hessZMat_mul hω h2 h3, hessZMat_mul_hessWMat_mul hω h2 h3]

@[expose] def hessCMat : Matrix (Fin 3) (Fin 3) F := fun i j => if i = j + 1 then 1 else 0

theorem hessCMat_mul_transpose : hessCMat (F := F) * hessCMatᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hessCMat]

theorem hessCMat_transpose_mul : hessCMatᵀ * hessCMat (F := F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hessCMat]

@[expose] def hessC : GL (Fin 3) F :=
  ⟨hessCMat, hessCMatᵀ, hessCMat_mul_transpose, hessCMat_transpose_mul⟩

theorem coe_hessC : ((hessC : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = hessCMat :=
  rfl

@[expose] def hessDeltaMat (ω : F) : Matrix (Fin 3) (Fin 3) F := diagonal ![1, ω, ω ^ 2]

theorem hessPhi_conj_hessC (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    ((hessPhi hω h3 * hessC * (hessPhi hω h3)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      hessDeltaMat ω := by
  simp only [Units.val_mul, coe_hessPhi, coe_hessPhi_inv, coe_hessC]
  have h1 := one_add_two_mul_ne_zero hω h3
  have h1' := one_add_two_mul_sq_ne_zero hω h3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessPhiMat, hessPhiInvMat, hessCMat,
      hessDeltaMat, Matrix.diagonal] <;>
    field_simp <;>
    grind

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
