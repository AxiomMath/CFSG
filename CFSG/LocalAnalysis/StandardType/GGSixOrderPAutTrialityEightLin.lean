module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.StandardType

namespace OrdPTriEight

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Nil

variable {N : Module.End K V} {U : Submodule K V}

theorem map_pow_succ_le (hU : U.map N ≤ U) (k : ℕ) : U.map (N ^ (k + 1)) ≤ U.map (N ^ k) := by
  rw [pow_succ, Module.End.mul_eq_comp, Submodule.map_comp]
  exact Submodule.map_mono hU

theorem map_pow_succ_eq (k : ℕ) : U.map (N ^ (k + 1)) = (U.map (N ^ k)).map N := by
  rw [pow_succ', Module.End.mul_eq_comp, Submodule.map_comp]

theorem map_pow_add_eq {k : ℕ} (h : U.map (N ^ (k + 1)) = U.map (N ^ k)) (j : ℕ) :
    U.map (N ^ (k + j)) = U.map (N ^ k) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [← add_assoc, map_pow_succ_eq, ih, ← map_pow_succ_eq, h]

theorem exists_ne_zero_apply_eq_zero (hU : U.map N ≤ U) (j : ℕ) :
    ∀ u ∈ U, (N ^ j) u = 0 → u ≠ 0 → ∃ w ∈ U, w ≠ 0 ∧ N w = 0 := by
  induction j with
  | zero => exact fun u _ hj hu0 => absurd (by rwa [pow_zero, Module.End.one_apply] at hj) hu0
  | succ j ih =>
    intro u hu hj hu0
    by_cases hNu : N u = 0
    · exact ⟨u, hu, hu0, hNu⟩
    · exact ih (N u) (hU (Submodule.mem_map_of_mem hu))
        (by rwa [pow_succ, Module.End.mul_apply] at hj) hNu

variable [FiniteDimensional K V]

theorem finrank_map_pow_succ_lt (hU : U.map N ≤ U) {m : ℕ} (hm : ∀ u ∈ U, (N ^ m) u = 0)
    {k : ℕ} (hk : U.map (N ^ k) ≠ ⊥) :
    finrank K (U.map (N ^ (k + 1))) < finrank K (U.map (N ^ k)) := by
  refine lt_of_le_of_ne (Submodule.finrank_mono (map_pow_succ_le hU k)) fun heq => hk ?_
  rw [← map_pow_add_eq (Submodule.eq_of_le_of_finrank_eq (map_pow_succ_le hU k) heq) m,
    eq_bot_iff]
  rintro _ ⟨u, hu, rfl⟩
  rw [Submodule.mem_bot, pow_add, Module.End.mul_apply, hm u hu, map_zero]

theorem finrank_map_pow_add_le (hU : U.map N ≤ U) {m : ℕ} (hm : ∀ u ∈ U, (N ^ m) u = 0)
    (k : ℕ) (hk : U.map (N ^ k) ≠ ⊥) : finrank K (U.map (N ^ k)) + k ≤ finrank K U := by
  induction k with
  | zero => rw [pow_zero, Module.End.one_eq_id, Submodule.map_id, add_zero]
  | succ k ih =>
    have hk' : U.map (N ^ k) ≠ ⊥ := fun h => hk (eq_bot_iff.2 ((map_pow_succ_le hU k).trans h.le))
    have h1 := finrank_map_pow_succ_lt hU hm hk'
    have h2 := ih hk'
    omega

theorem pow_apply_eq_zero_of_finrank_le (hU : U.map N ≤ U) {m : ℕ}
    (hm : ∀ u ∈ U, (N ^ m) u = 0) {n : ℕ} (hn : finrank K U ≤ n) {u : V} (hu : u ∈ U) :
    (N ^ n) u = 0 := by
  by_contra hne
  have hbot : U.map (N ^ n) ≠ ⊥ := fun hb => hne (by
    have h := Submodule.mem_map_of_mem (f := N ^ n) hu
    rwa [hb, Submodule.mem_bot] at h)
  have h1 := finrank_map_pow_add_le hU hm n hbot
  have h2 := Submodule.one_le_finrank_iff.2 hbot
  omega

end Nil

theorem two_mul_finrank_le_of_isotropic [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    (hB : B.Nondegenerate) {U : Submodule K V} (hU : ∀ u ∈ U, ∀ w ∈ U, B u w = 0) :
    2 * finrank K U ≤ finrank K V := by
  have hle : U ≤ B.orthogonal U := fun w hw =>
    LinearMap.BilinForm.mem_orthogonal_iff.2 fun u hu => hU u hu w hw
  have h1 := LinearMap.BilinForm.finrank_orthogonal hB U
  have h2 := Submodule.finrank_mono hle
  have h3 := Submodule.finrank_le U
  omega

section CharTwo

variable [CharP K 2]

theorem end_two_eq_zero : (2 : Module.End K V) = 0 := by
  rw [← one_add_one_eq_two, ← two_smul K (1 : Module.End K V), CharTwo.two_eq_zero, zero_smul]

theorem sub_one_sq (x : Module.End K V) : (x - 1) ^ 2 = x ^ 2 - 1 := by
  have h : (x - 1) ^ 2 = x ^ 2 - 1 - 2 * (x - 1) := by noncomm_ring
  rw [h, end_two_eq_zero, zero_mul, sub_zero]

theorem sub_one_pow_four (x : Module.End K V) : (x - 1) ^ 4 = x ^ 4 - 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sub_one_sq, sub_one_sq, ← pow_mul]

theorem sub_one_pow_eight (x : Module.End K V) : (x - 1) ^ 8 = x ^ 8 - 1 := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, sub_one_pow_four, sub_one_sq, ← pow_mul]

end CharTwo

end OrdPTriEight

end CFSG.StandardType
