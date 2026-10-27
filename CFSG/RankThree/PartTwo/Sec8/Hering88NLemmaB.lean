module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.CharP.Algebra

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open Polynomial

theorem matrix_pow_two_pow_eq_one {F : Type*} [Field F] [CharP F 2] {n j : ℕ} (hn : n ≤ 2 ^ j)
    {u : Matrix (Fin n) (Fin n) F} (h2 : ∃ k : ℕ, u ^ 2 ^ k = 1) : u ^ 2 ^ j = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · exact Subsingleton.elim _ _
  haveI : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  haveI : CharP (Matrix (Fin n) (Fin n) F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (Matrix (Fin n) (Fin n) F)).injective 2
  obtain ⟨k, hk⟩ := h2
  have hN : IsNilpotent (u - 1) := ⟨2 ^ k, by
    rw [sub_pow_char_pow_of_commute (p := 2) (h := Commute.one_right u), one_pow, hk, sub_self]⟩
  have hcp : (u - 1).charpoly = X ^ n := by
    have h := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN).eq_zero
    simpa [sub_eq_zero] using h
  have hn0 : (u - 1) ^ n = 0 := by
    have h := Matrix.aeval_self_charpoly (u - 1)
    rw [hcp] at h
    simpa using h
  have h4 : (u - 1) ^ 2 ^ j = 0 := by
    rw [show 2 ^ j = (2 ^ j - n) + n by omega, pow_add, hn0, mul_zero]
  have e : (u - 1) ^ 2 ^ j = u ^ 2 ^ j - 1 := by
    rw [sub_pow_char_pow_of_commute (p := 2) (h := Commute.one_right u), one_pow]
  rw [e, sub_eq_zero] at h4
  exact h4

theorem sl2_pow_two_eq_one {F : Type*} [Field F] [CharP F 2]
    (s : Matrix.SpecialLinearGroup (Fin 2) F) (h2 : ∃ k : ℕ, s ^ 2 ^ k = 1) : s ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := h2
  have h : ((s : Matrix (Fin 2) (Fin 2) F)) ^ 2 ^ 1 = 1 :=
    matrix_pow_two_pow_eq_one (by norm_num) ⟨k, by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hk, Matrix.SpecialLinearGroup.coe_one]⟩
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  rw [pow_one] at h
  rw [h]

theorem gl3_pow_four_eq_one {F : Type*} [Field F] [CharP F 2] (u : GL (Fin 3) F)
    (h2 : ∃ k : ℕ, u ^ 2 ^ k = 1) : u ^ 4 = 1 := by
  obtain ⟨k, hk⟩ := h2
  have h : ((u : Matrix (Fin 3) (Fin 3) F)) ^ 2 ^ 2 = 1 :=
    matrix_pow_two_pow_eq_one (by norm_num) ⟨k, by rw [← Units.val_pow_eq_pow_val, hk]; rfl⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  simpa using h

theorem pow_two_pow_eq_one_of_mem_range {H Q : Type*} [Group H] [Group Q] [Finite H]
    (φ : H →* Q) {j : ℕ} (hH : ∀ t : H, (∃ k : ℕ, t ^ 2 ^ k = 1) → t ^ 2 ^ j = 1) {y : Q}
    (hy : y ∈ φ.range) (h2 : ∃ k : ℕ, y ^ 2 ^ k = 1) : y ^ 2 ^ j = 1 := by
  obtain ⟨s, rfl⟩ := hy
  obtain ⟨k, hk⟩ := h2
  have hn0 : orderOf s ≠ 0 := (orderOf_pos s).ne'
  obtain ⟨e, r, hr, hn⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have ht : (s ^ r) ^ 2 ^ j = 1 := hH _ ⟨e, by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]⟩
  have h1 : φ s ^ (r * 2 ^ j) = 1 := by rw [pow_mul, ← map_pow, ← map_pow, ht, map_one]
  have h3 := pow_gcd_eq_one.mpr ⟨h1, hk⟩
  have hcop : Nat.Coprime r (2 ^ k) := Nat.Coprime.pow_right k hr.coprime_two_right
  rw [Nat.Coprime.gcd_mul_left_cancel _ hcop] at h3
  obtain ⟨c, hc⟩ := Nat.gcd_dvd_left (2 ^ j) (2 ^ k)
  rw [hc, pow_mul, h3, one_pow]

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
