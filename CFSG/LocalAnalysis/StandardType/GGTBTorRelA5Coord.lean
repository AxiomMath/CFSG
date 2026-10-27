module

public import CFSG.LocalAnalysis.StandardType.GGTorusScalar

@[expose] public section

namespace CFSG.StandardType.RelA5

theorem cartanC_three : CartanMatrix.C 3 = !![2, -1, 0; -1, 2, -1; 0, -2, 2] := by
  decide

variable {μ : Type} [CommGroup μ]

def root : (Fin 3 → μ) →* (Fin 3 → μ) where
  toFun z := ![z 0 / z 1, z 1 / z 2, z 2 ^ 2]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' z w := by
    funext i
    fin_cases i <;> simp [div_mul_div_comm, mul_pow]

@[simp] theorem root_apply_zero (z : Fin 3 → μ) : root z 0 = z 0 / z 1 := rfl
@[simp] theorem root_apply_one (z : Fin 3 → μ) : root z 1 = z 1 / z 2 := rfl
@[simp] theorem root_apply_two (z : Fin 3 → μ) : root z 2 = z 2 ^ 2 := rfl

def corBlockFun (k : Fin 3) (ζ : μ) : Fin 3 → μ :=
  match k with
  | 0 => ![ζ, ζ⁻¹, 1]
  | 1 => ![1, ζ, ζ⁻¹]
  | 2 => ![1, 1, ζ]

def corBlock (k : Fin 3) : μ →* (Fin 3 → μ) where
  toFun := corBlockFun k
  map_one' := by
    funext i
    fin_cases k <;> fin_cases i <;> simp [corBlockFun]
  map_mul' ζ ξ := by
    funext i
    fin_cases k <;> fin_cases i <;> simp [corBlockFun, mul_comm]

@[simp] theorem corBlock_apply (k : Fin 3) (ζ : μ) : corBlock k ζ = corBlockFun k ζ := rfl

theorem root_corBlock (k : Fin 3) (ζ : μ) :
    root (corBlock k ζ) = corTuple (CartanMatrix.C 3).transpose k ζ := by
  funext i
  rw [corTuple_apply, Matrix.transpose_apply, cartanC_three]
  fin_cases k <;> fin_cases i <;>
    simp [corBlockFun, root, zpow_neg, zpow_ofNat, sq, div_eq_mul_inv]

def refl (k : Fin 3) (z : Fin 3 → μ) : Fin 3 → μ :=
  match k with
  | 0 => ![z 1, z 0, z 2]
  | 1 => ![z 0, z 2, z 1]
  | 2 => ![z 0, z 1, (z 2)⁻¹]

theorem refl_eq (k : Fin 3) (z : Fin 3 → μ) : refl k z = z * (corBlock k (root z k))⁻¹ := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [refl, corBlockFun, root, div_eq_mul_inv, sq, mul_comm, mul_left_comm]

section Inv

variable {m : ℕ} (hm : Odd m) (hμ : ∀ x : μ, x ^ m = 1)
include hm hμ

theorem pow_half_sq (x : μ) : (x ^ ((m + 1) / 2)) ^ 2 = x := by
  obtain ⟨k, rfl⟩ := hm
  rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, ← pow_mul,
    show (k + 1) * 2 = (2 * k + 1) + 1 by ring, pow_succ, hμ x, one_mul]

theorem sq_pow_half (x : μ) : (x ^ 2) ^ ((m + 1) / 2) = x := by
  rw [← pow_mul, mul_comm, pow_mul, pow_half_sq hm hμ]

end Inv

def rootInv (m : ℕ) : (Fin 3 → μ) →* (Fin 3 → μ) where
  toFun b := ![b 0 * b 1 * b 2 ^ ((m + 1) / 2), b 1 * b 2 ^ ((m + 1) / 2), b 2 ^ ((m + 1) / 2)]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' b c := by
    funext i
    fin_cases i <;> simp [mul_pow, mul_left_comm, mul_assoc]

section InvProps

variable {m : ℕ} (hm : Odd m) (hμ : ∀ x : μ, x ^ m = 1)
include hm hμ

theorem root_rootInv (b : Fin 3 → μ) : root (rootInv m b) = b := by
  funext i
  fin_cases i
  · simp [rootInv, root, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  · simp [rootInv, root, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  · simp only [rootInv, root, MonoidHom.coe_mk, OneHom.coe_mk, Fin.isValue,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    exact pow_half_sq hm hμ (b 2)

theorem rootInv_root (z : Fin 3 → μ) : rootInv m (root z) = z := by
  have h2 : (z 2 ^ 2) ^ ((m + 1) / 2) = z 2 := sq_pow_half hm hμ (z 2)
  funext i
  fin_cases i
  · simp [rootInv, root, h2, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  · simp [rootInv, root, h2, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  · simp [rootInv, root, h2]

theorem rootInv_corTuple (k : Fin 3) (ζ : μ) :
    rootInv m (corTuple (CartanMatrix.C 3).transpose k ζ) = corBlock k ζ := by
  rw [← root_corBlock, rootInv_root hm hμ]

theorem rootInv_injective : Function.Injective (rootInv (μ := μ) m) := fun b c h => by
  rw [← root_rootInv hm hμ b, ← root_rootInv hm hμ c, h]

end InvProps

end CFSG.StandardType.RelA5
