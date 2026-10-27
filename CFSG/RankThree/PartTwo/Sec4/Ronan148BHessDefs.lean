module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix

variable {F : Type*} [Field F]

@[expose] def hessTMat (i : Fin 3) : Matrix (Fin 3) (Fin 3) F :=
  diagonal fun j => if j = i then 1 else -1

theorem hessTMat_mul_self (i : Fin 3) : hessTMat (F := F) i * hessTMat i = 1 := by
  rw [hessTMat, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

@[expose] def hessT (i : Fin 3) : GL (Fin 3) F :=
  ⟨hessTMat i, hessTMat i, hessTMat_mul_self i, hessTMat_mul_self i⟩

theorem coe_hessT (i : Fin 3) :
    ((hessT i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = hessTMat i :=
  rfl

@[expose] def hessPhiMat (ω : F) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => ω ^ (i.val * j.val) / (1 + 2 * ω)

@[expose] def hessPhiInvMat (ω : F) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => ω ^ (2 * (i.val * j.val)) / (1 + 2 * ω ^ 2)

variable {ω : F}

theorem pow_three_eq_one_of_hess (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

theorem one_add_two_mul_ne_zero (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    1 + 2 * ω ≠ 0 := by
  intro h
  apply h3
  linear_combination (-(1 : F) - 2 * ω) * h + 4 * hω

theorem one_add_two_mul_sq_ne_zero (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    1 + 2 * ω ^ 2 ≠ 0 := by
  intro h
  apply one_add_two_mul_ne_zero hω h3
  linear_combination -h + 2 * hω

theorem hessPhiMat_mul_inv (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    hessPhiMat ω * hessPhiInvMat ω = 1 := by
  have h1 := one_add_two_mul_ne_zero hω h3
  have h2 := one_add_two_mul_sq_ne_zero hω h3
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessPhiMat, hessPhiInvMat, Matrix.one_apply] <;>
    field_simp <;>
    grind

theorem hessPhiInvMat_mul (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    hessPhiInvMat ω * hessPhiMat ω = 1 := by
  have h1 := one_add_two_mul_ne_zero hω h3
  have h2 := one_add_two_mul_sq_ne_zero hω h3
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessPhiMat, hessPhiInvMat, Matrix.one_apply] <;>
    field_simp <;>
    grind

@[expose] def hessPhi (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) : GL (Fin 3) F :=
  ⟨hessPhiMat ω, hessPhiInvMat ω, hessPhiMat_mul_inv hω h3, hessPhiInvMat_mul hω h3⟩

theorem coe_hessPhi (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    ((hessPhi hω h3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = hessPhiMat ω :=
  rfl

theorem coe_hessPhi_inv (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    (((hessPhi hω h3)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = hessPhiInvMat ω :=
  rfl

end CFSG.RankThree.PartTwo.Sec4.Ronan148B

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix

@[expose] def HessPhiMemClosure : Prop :=
  ∀ (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p], 5 ≤ p →
    ∀ (ω : F) (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0),
      hessPhi hω h3 ∈ Subgroup.closure
        (Set.range (hessT (F := F)) ∪
          Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹)

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
