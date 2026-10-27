module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitary_full_diagonal_outer_order)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem unitary_outer_order_divides_field_norm_one_bound {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    Nat.card (Outer (unitaryPSU h n)) ∣ 2 * f * (ℓ ^ f + 1) := by
  rw [(unitary_full_diagonal_outer_order h hn hq).2.2.2.2.1]
  exact mul_dvd_mul_left _ (Nat.gcd_dvd_right _ _)

end CFSG.RankThree.Automorphisms
