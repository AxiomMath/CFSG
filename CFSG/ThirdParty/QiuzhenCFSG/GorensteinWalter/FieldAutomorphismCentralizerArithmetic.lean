module

public import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Arithmetic obstruction for prime-order field centralizers

The two equations arising from the fixed-field centralizer calculation are
impossible as soon as the fixed field and automorphism order are at least
three.
-/

namespace CFSG.GorensteinWalter

/-- Neither `r ^ p + 1 = p(r + 1)` nor `r ^ p - 1 = p(r - 1)` can hold
for `r, p >= 3`. -/
public theorem fieldAutomorphism_centralizer_equations_impossible
    (r p : ℕ) (hr : 3 ≤ r) (hp : 3 ≤ p) :
    r ^ p + 1 ≠ p * (r + 1) ∧
      r ^ p - 1 ≠ p * (r - 1) := by
  have hstrong : p * (r + 1) < r ^ p - 1 := by
    have hbase : 3 * (r + 1) + 2 ≤ r ^ 3 := by
      have hsq : 3 * 3 ≤ r * r := Nat.mul_le_mul hr hr
      have hcub := Nat.mul_le_mul_right r hsq
      norm_num [pow_succ] at hcub ⊢
      nlinarith
    have hmain : p * (r + 1) + 2 ≤ r ^ p := by
      induction p, hp using Nat.le_induction with
      | base => exact hbase
      | succ n _hn ih =>
          have har := Nat.mul_le_mul_right r ih
          rw [pow_succ]
          nlinarith
    omega
  have hminusle : p * (r - 1) ≤ p * (r + 1) :=
    Nat.mul_le_mul_left p (by omega)
  constructor <;> omega

/-! A monotone form of the same obstruction is convenient when the
semilinear centralizer calculation only gives an upper bound for the fixed
part, rather than its exact cardinality. -/

public theorem fieldAutomorphism_centralizer_upper_bound_impossible
    (r p : ℕ) (hr : 3 ≤ r) (hp : 3 ≤ p) :
    ¬ (r ^ p + 1 ≤ p * (r + 1)) ∧
      ¬ (r ^ p - 1 ≤ p * (r - 1)) := by
  have hstrong : p * (r + 1) < r ^ p - 1 := by
    have hbase : 3 * (r + 1) + 2 ≤ r ^ 3 := by
      have hsq : 3 * 3 ≤ r * r := Nat.mul_le_mul hr hr
      have hcub := Nat.mul_le_mul_right r hsq
      norm_num [pow_succ] at hcub ⊢
      nlinarith
    have hmain : p * (r + 1) + 2 ≤ r ^ p := by
      induction p, hp using Nat.le_induction with
      | base => exact hbase
      | succ n _hn ih =>
          have har := Nat.mul_le_mul_right r ih
          rw [pow_succ]
          nlinarith
    omega
  have hminusle : p * (r - 1) ≤ p * (r + 1) :=
    Nat.mul_le_mul_left p (by omega)
  constructor <;> omega

end CFSG.GorensteinWalter
