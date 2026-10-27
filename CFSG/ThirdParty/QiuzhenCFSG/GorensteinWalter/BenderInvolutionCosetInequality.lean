module

import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Bender's involution/coset inequality

Section 2 of Bender's *Finite groups with large subgroups* counts
involutions in the non-base cosets of a subgroup.  The theorem below is the
division-free aggregate form of Lemma (3).

Here `singleCosets` is Bender's `b₁`, `multipleCosets` is
`∑ n ≥ 2, bₙ`, and `extraInvolutions` is `∑ n ≥ 2, (n - 1) bₙ`.
Thus the total involution count is

`internalInvolutions + singleCosets + multipleCosets + extraInvolutions`.

The equation involving `ratioNumerator` and `ratioDenominator` represents

`f = |J| / |G : H| - 1 = ratioNumerator / ratioDenominator`

without division.
-/

namespace CFSG.GorensteinWalter

/-- Bender's generic involution/coset inequality, in division-free form.

The first hypothesis says that the base coset together with all cosets
containing at least one involution accounts for no more than the full coset
space.  The second is the aggregate involution-count identity.  After
encoding `f = |J| / |G : H| - 1` by the final multiplication identity, the
conclusion is equivalent to

`b₁ < f⁻¹ (|J ∩ H| + b₂ + 2b₃ + ⋯) - 1 - b₂ - b₃ - ⋯`.
-/
public theorem bender_involution_coset_inequality
    (cosetIndex involutions internalInvolutions singleCosets
      multipleCosets extraInvolutions ratioNumerator ratioDenominator : ℕ)
    (hcosets :
      1 + singleCosets + multipleCosets ≤ cosetIndex)
    (hcount :
      involutions = internalInvolutions + singleCosets +
        multipleCosets + extraInvolutions)
    (hlarge : cosetIndex < involutions)
    (hdenominator : 0 < ratioDenominator)
    (hratio :
      ratioDenominator * (involutions - cosetIndex) =
        ratioNumerator * cosetIndex) :
    ratioNumerator * (singleCosets + 1 + multipleCosets) <
      ratioDenominator * (internalInvolutions + extraInvolutions) := by
  have hindex : 0 < cosetIndex := by omega
  have hsub : cosetIndex + (involutions - cosetIndex) = involutions :=
    Nat.add_sub_of_le (Nat.le_of_lt hlarge)
  have hexcess_lt :
      involutions - cosetIndex < internalInvolutions + extraInvolutions := by
    omega
  have hpositive : 0 < singleCosets + 1 + multipleCosets := by omega
  have hbase :
      (involutions - cosetIndex) *
          (singleCosets + 1 + multipleCosets) <
        cosetIndex * (internalInvolutions + extraInvolutions) := by
    calc
      (involutions - cosetIndex) *
            (singleCosets + 1 + multipleCosets) <
          (internalInvolutions + extraInvolutions) *
            (singleCosets + 1 + multipleCosets) :=
        Nat.mul_lt_mul_of_pos_right hexcess_lt hpositive
      _ ≤ (internalInvolutions + extraInvolutions) * cosetIndex :=
        Nat.mul_le_mul_left _ (by omega)
      _ = cosetIndex * (internalInvolutions + extraInvolutions) := by
        rw [Nat.mul_comm]
  have hscaled := Nat.mul_lt_mul_of_pos_left hbase hdenominator
  have hcancel :
      cosetIndex *
          (ratioNumerator * (singleCosets + 1 + multipleCosets)) <
        cosetIndex *
          (ratioDenominator * (internalInvolutions + extraInvolutions)) := by
    calc
      cosetIndex *
            (ratioNumerator * (singleCosets + 1 + multipleCosets)) =
          ratioDenominator *
            ((involutions - cosetIndex) *
              (singleCosets + 1 + multipleCosets)) := by
        calc
          cosetIndex *
                (ratioNumerator * (singleCosets + 1 + multipleCosets)) =
              (ratioNumerator * cosetIndex) *
                (singleCosets + 1 + multipleCosets) := by ring
          _ = (ratioDenominator * (involutions - cosetIndex)) *
                (singleCosets + 1 + multipleCosets) := by rw [hratio]
          _ = ratioDenominator *
                ((involutions - cosetIndex) *
                  (singleCosets + 1 + multipleCosets)) := by ring
      _ < ratioDenominator *
            (cosetIndex * (internalInvolutions + extraInvolutions)) := hscaled
      _ = cosetIndex *
            (ratioDenominator *
              (internalInvolutions + extraInvolutions)) := by
        ring
  exact (Nat.mul_lt_mul_left hindex).mp hcancel

end CFSG.GorensteinWalter
