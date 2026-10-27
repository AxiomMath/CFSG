module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem higher_linear_outer_order_divides_field_scalar_bound {K : Type} [Field K] {ℓ f n : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hn : 3 ≤ n) (hK : Nat.card K = ℓ ^ f) :
    Nat.card (Outer (projectiveSL n K)) ∣ 2 * f * (ℓ ^ f - 1) :=
  (higher_linear_outer_order_divides_field_gcd_bound hℓ hf hn hK).trans
    (mul_dvd_mul_left _ (Nat.gcd_dvd_right _ _))

end CFSG.RankThree.Automorphisms
