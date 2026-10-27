module

public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartOne.KLCE

variable {G : Type*} [Group G]

theorem pow_mul_conj_fixed {n a : G} {m : ℕ} (h : n ^ m * a * (n ^ m)⁻¹ = a) (k : ℕ) :
    n ^ (m * k) * a * (n ^ (m * k))⁻¹ = a := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc n ^ (m * (k + 1)) * a * (n ^ (m * (k + 1)))⁻¹
        = n ^ (m * k) * (n ^ m * a * (n ^ m)⁻¹) * (n ^ (m * k))⁻¹ := by
          rw [mul_add, mul_one, pow_add]; group
      _ = a := by rw [h, ih]

theorem pow_mul_add_conj {n a : G} {m : ℕ} (h : n ^ m * a * (n ^ m)⁻¹ = a) (k j : ℕ) :
    n ^ (m * k + j) * a * (n ^ (m * k + j))⁻¹ = n ^ j * a * (n ^ j)⁻¹ := by
  rw [add_comm, pow_add]
  calc n ^ j * n ^ (m * k) * a * (n ^ j * n ^ (m * k))⁻¹
      = n ^ j * (n ^ (m * k) * a * (n ^ (m * k))⁻¹) * (n ^ j)⁻¹ := by group
    _ = n ^ j * a * (n ^ j)⁻¹ := by rw [pow_mul_conj_fixed h k]

theorem pow_odd_conj_swap {n a b : G} (hab : n * a * n⁻¹ = b) (hba : n * b * n⁻¹ = a) (k : ℕ) :
    n ^ (2 * k + 1) * a * (n ^ (2 * k + 1))⁻¹ = b := by
  have h2 : n ^ 2 * a * (n ^ 2)⁻¹ = a := by
    calc n ^ 2 * a * (n ^ 2)⁻¹ = n * (n * a * n⁻¹) * n⁻¹ := by rw [pow_two]; group
      _ = a := by rw [hab, hba]
  rw [pow_mul_add_conj h2 k 1, pow_one, hab]

theorem pow_three_succ_conj {n a b c : G} (hab : n * a * n⁻¹ = b) (hbc : n * b * n⁻¹ = c)
    (hca : n * c * n⁻¹ = a) (k : ℕ) :
    n ^ (3 * k + 1) * a * (n ^ (3 * k + 1))⁻¹ = b := by
  have h3 : n ^ 3 * a * (n ^ 3)⁻¹ = a := by
    calc n ^ 3 * a * (n ^ 3)⁻¹ = n * (n * (n * a * n⁻¹) * n⁻¹) * n⁻¹ := by
          rw [pow_succ, pow_two]; group
      _ = a := by rw [hab, hbc, hca]
  rw [pow_mul_add_conj h3 k 1, pow_one, hab]

end CFSG.RankThree.PartOne.KLCE
