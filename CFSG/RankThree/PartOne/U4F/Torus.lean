module

public import CFSG.RankThree.PartOne.KF.R5Levi2
public import CFSG.RankThree.PartOne.KF.SUGram

public section

namespace CFSG.RankThree.PartOne.U4F

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KFU
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive unitaryInvolution_apply)

variable {K : Type} [Field K] {f : ℕ}

theorem fix_of_pow_eq_one [Finite K] [CharP K 2] {r : ℕ} (hr : r ∣ 2 ^ f - 1) {u : Kˣ}
    (hu : u ^ r = 1) :
    unitaryInvolution K 2 f (u : K) = u := by
  have hσ : ∀ c : K, unitaryInvolution K 2 f c = c ^ 2 ^ f := fun c =>
    unitaryInvolution_apply K 2 f c
  have h2 : u ^ (2 ^ f - 1) = 1 := by
    obtain ⟨k, hk⟩ := hr
    rw [hk, pow_mul, hu, one_pow]
  rw [hσ, ← Units.val_pow_eq_pow_val]
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have : u ^ 2 ^ f = u := by
    calc u ^ 2 ^ f = u ^ (2 ^ f - 1) * u := by rw [← pow_succ, Nat.sub_add_cancel hq1]
      _ = u := by rw [h2, one_mul]
  rw [this]

variable [CharP K 2] (σ : K ≃+* K)

@[expose] noncomputable def piU : ↥(SU σ 4) :=
  ⟨permGL (Equiv.swap (1 : Fin 4) 2), permGL_mem_SU σ _ (by decide)⟩

@[expose] noncomputable def omU : ↥(SU σ 4) :=
  ⟨permGL (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3), permGL_mem_SU σ _ (by decide)⟩

theorem coe_piU : ((piU σ : ↥(SU σ 4)) : GL (Fin 4) K) = permGL (Equiv.swap (1 : Fin 4) 2) := rfl

theorem coe_omU : ((omU σ : ↥(SU σ 4)) : GL (Fin 4) K) =
    permGL (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) := rfl

theorem piU_conj_diag (a b : Kˣ) :
    ((piU σ : ↥(SU σ 4)) : GL (Fin 4) K) * diagU (dvec4 a b) *
      ((piU σ : ↥(SU σ 4)) : GL (Fin 4) K)⁻¹ = diagU (dvec4 a b⁻¹) := by
  rw [coe_piU, permGL_conj_diagU]
  congr 1
  funext i
  fin_cases i <;> simp [dvec4, Equiv.swap_apply_def]

theorem omU_conj_diag (a b : Kˣ) :
    ((omU σ : ↥(SU σ 4)) : GL (Fin 4) K) * diagU (dvec4 a b) *
      ((omU σ : ↥(SU σ 4)) : GL (Fin 4) K)⁻¹ = diagU (dvec4 b a) := by
  rw [coe_omU, permGL_conj_diagU]
  have hω : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3).symm =
      Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 := by decide
  congr 1
  funext i
  rw [Function.comp_apply, hω]
  fin_cases i <;> simp [dvec4, Equiv.swap_apply_def, Equiv.Perm.mul_apply]

@[expose] def wK : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two]; simp [CharTwo.neg_eq]⟩

theorem omU_eq_suBlockB (hσσ : ∀ x, σ (σ x) = x) : omU σ = suBlockB σ hσσ wK := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_omU, coe_suBlockB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_permGL, blkB, wK, Equiv.Perm.inv_def, Equiv.swap_apply_def, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Matrix.mul_apply, Fin.sum_univ_four]

theorem piU_mul_self : piU σ * piU σ = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_piU, ← map_mul, Equiv.swap_mul_self, map_one]
  rfl

theorem piU_inv : (piU σ)⁻¹ = piU σ := inv_eq_of_mul_eq_one_right (piU_mul_self σ)

theorem omU_mem_range (hσσ : ∀ x, σ (σ x) = x) : omU σ ∈ (suBlockB σ hσσ).range :=
  ⟨wK, (omU_eq_suBlockB σ hσσ).symm⟩

end CFSG.RankThree.PartOne.U4F
