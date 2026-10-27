module

public import CFSG.Monster.B.Dyadic.FixedLine

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Dyadic

open Module
open scoped Matrix

section Generic

variable {K : Type*} [Field K] {n : ℕ}

theorem finrank_ker_add_rank (A : Matrix (Fin n) (Fin n) K) :
    finrank K (LinearMap.ker A.mulVecLin) + A.rank = n := by
  rw [Matrix.rank, add_comm, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]

theorem isCompl_ker_of {a b c : Matrix (Fin n) (Fin n) K} (hab : a * b = 0)
    (hbca : b * c * a = 0) (h1 : b - c * a = 1) :
    IsCompl (LinearMap.ker a.mulVecLin) (LinearMap.ker b.mulVecLin) := by
  have hv : ∀ v : Fin n → K, v = b *ᵥ v - c *ᵥ (a *ᵥ v) := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Matrix.sub_mulVec, h1, Matrix.one_mulVec]
  constructor
  · rw [Submodule.disjoint_def]
    intro v ha hb
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at ha hb
    rw [hv v, ha, hb, Matrix.mulVec_zero, sub_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [hv v]
    refine Submodule.sub_mem_sup ?_ ?_
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hab,
        Matrix.zero_mulVec]
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        hbca, Matrix.zero_mulVec]

theorem finrank_ker_of {a b c : Matrix (Fin n) (Fin n) K} (hab : a * b = 0)
    (hbca : b * c * a = 0) (h1 : b - c * a = 1) :
    finrank K (LinearMap.ker b.mulVecLin) = a.rank := by
  have h := Submodule.finrank_add_eq_of_isCompl (isCompl_ker_of hab hbca h1)
  have h' := finrank_ker_add_rank a
  rw [Module.finrank_fin_fun] at h
  omega

end Generic

section Ring

variable {A : Type*} [Ring A]

theorem quad_mul_mul_sub_one {q : A} (hq : q * q * q = 1) :
    (q * q + q + 1) * q * (q - 1) = 0 := by
  have h : (q * q + q + 1) * q * (q - 1) = q * (q * q * q) - q := by noncomm_ring
  rw [h, hq, mul_one, sub_self]

theorem quad_sub_mul_sub_one (h2 : (2 : A) = 0) (q : A) : (q * q + q + 1) - q * (q - 1) = 1 := by
  have h : (q * q + q + 1) - q * (q - 1) = 2 * q + 1 := by noncomm_ring
  rw [h, h2, zero_mul, zero_add]

end Ring

theorem orderOf_Q0 : orderOf (Qmat 0) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact Q0_sq) Q0_ne_one

theorem orderOf_Q25 : orderOf (Qmat 25) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by rw [pow_three']; exact Q25_cube) Q25_ne_one

theorem finrank_ker_Q0_sub_one :
    finrank (ZMod 2) (LinearMap.ker (Qmat 0 - 1).mulVecLin) = 1860 + 650 := by
  have h := finrank_ker_add_rank (Qmat 0 - 1)
  rw [rank_Q0] at h
  exact Nat.eq_sub_of_add_eq h

theorem range_le_ker_Q0 :
    LinearMap.range (Qmat 0 - 1).mulVecLin ≤ LinearMap.ker (Qmat 0 - 1).mulVecLin := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    Q0_sub_one_sq, Matrix.zero_mulVec]

theorem finrank_ker_Q25_sub_one :
    finrank (ZMod 2) (LinearMap.ker (Qmat 25 - 1).mulVecLin) = 1508 := by
  have h := finrank_ker_add_rank (Qmat 25 - 1)
  rw [rank_Q25] at h
  exact Nat.eq_sub_of_add_eq h

theorem Q25_quad_mul :
    (Qmat 25 * Qmat 25 + Qmat 25 + 1) * Qmat 25 * (Qmat 25 - 1) = 0 :=
  quad_mul_mul_sub_one (A := Matrix (Fin 4370) (Fin 4370) (ZMod 2)) Q25_cube

theorem Q25_quad_sub : (Qmat 25 * Qmat 25 + Qmat 25 + 1) - Qmat 25 * (Qmat 25 - 1) = 1 :=
  quad_sub_mul_sub_one (A := Matrix (Fin 4370) (Fin 4370) (ZMod 2)) two_eq_zero_mat (Qmat 25)

theorem isCompl_ker_Q25 :
    IsCompl (LinearMap.ker (Qmat 25 - 1).mulVecLin)
      (LinearMap.ker (Qmat 25 * Qmat 25 + Qmat 25 + 1).mulVecLin) :=
  isCompl_ker_of (K := ZMod 2) (n := 4370) (a := Qmat 25 - 1)
    (b := Qmat 25 * Qmat 25 + Qmat 25 + 1) (c := Qmat 25) Q25_sub_one_mul Q25_quad_mul Q25_quad_sub

theorem finrank_ker_Q25_quad :
    finrank (ZMod 2) (LinearMap.ker (Qmat 25 * Qmat 25 + Qmat 25 + 1).mulVecLin) = 2 * 1431 := by
  have h := finrank_ker_of (K := ZMod 2) (n := 4370) (a := Qmat 25 - 1)
    (b := Qmat 25 * Qmat 25 + Qmat 25 + 1) (c := Qmat 25) Q25_sub_one_mul Q25_quad_mul Q25_quad_sub
  rw [rank_Q25] at h
  exact h

theorem rank_Q25_quad :
    (Qmat 25 * Qmat 25 + Qmat 25 + 1).rank = 1508 := by
  have h := finrank_ker_add_rank (Qmat 25 * Qmat 25 + Qmat 25 + 1)
  have e : finrank (ZMod 2) (LinearMap.ker (Qmat 25 * Qmat 25 + Qmat 25 + 1).mulVecLin) = 2862 :=
    finrank_ker_Q25_quad
  have h' : 2862 + (Qmat 25 * Qmat 25 + Qmat 25 + 1).rank = 4370 := by
    rw [← e]
    exact h
  exact Nat.eq_sub_of_add_eq' h'

theorem quad_irreducible :
    Irreducible (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have h : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)).natDegree = 2 := by
      compute_degree!
    rw [h]
    decide
  · intro x
    rw [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide

end CFSG.Monster.B.Dyadic
