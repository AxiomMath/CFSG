module

public import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# A divisor bound for odd powers

If `r` and `p` are odd, then the common divisors of `r + 1` and
`(r ^ p + 1) / 2` already divide `(r + 1) / 2`.
-/

namespace CFSG.GorensteinWalter

open Finset

/-- For odd `r` and odd `p`, a number dividing both `r + 1` and half of
`r ^ p + 1` divides half of `r + 1`.

The quotient `(r ^ p + 1) / (r + 1)` is represented by the positive
alternating geometric sum in `ℤ`; it is odd because it contains an odd number
of odd summands. -/
public theorem dvd_add_one_half_of_dvd_odd_power_half
    (a r p : ℕ) (hr : Odd r) (hp : Odd p)
    (ha1 : a ∣ r + 1) (ha2 : a ∣ (r ^ p + 1) / 2) :
    a ∣ (r + 1) / 2 := by
  let z : ℤ := -(r : ℤ)
  let sZ : ℤ := ∑ i ∈ Finset.range p, z ^ i
  have hzOdd : Odd z := (hr.natCast (R := ℤ)).neg
  rcases hp with ⟨k, hk⟩
  have hpEq : p = 2 * k + 1 := by omega
  have hsZOddAux : ∀ j : ℕ,
      Odd (∑ i ∈ Finset.range (2 * j + 1), z ^ i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega]
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        exact (ih.add_odd hzOdd.pow).add_odd hzOdd.pow
  have hsZOdd : Odd sZ := by
    dsimp [sZ]
    rw [hpEq]
    exact hsZOddAux k
  have hsZpos : 0 < sZ := by
    dsimp [sZ]
    exact (show Odd p from ⟨k, hk⟩).geom_sum_pos
  let s : ℕ := sZ.toNat
  have hsCast : (s : ℤ) = sZ :=
    Int.toNat_of_nonneg hsZpos.le
  have hsOddZ : Odd (s : ℤ) := by
    rw [hsCast]
    exact hsZOdd
  have hsOdd : Odd s := by
    exact_mod_cast hsOddZ
  have hfactorZ : ((r + 1 : ℕ) : ℤ) * sZ =
      ((r ^ p + 1 : ℕ) : ℤ) := by
    have hgeom := geom_sum_mul z p
    change sZ * (z - 1) = z ^ p - 1 at hgeom
    rw [show z = -(r : ℤ) by rfl,
      Odd.neg_pow (show Odd p from ⟨k, hk⟩)] at hgeom
    push_cast
    nlinarith
  have hfactor : (r + 1) * s = r ^ p + 1 := by
    have hfactorZ' : (((r + 1) * s : ℕ) : ℤ) =
        ((r ^ p + 1 : ℕ) : ℤ) := by
      push_cast
      rw [hsCast]
      exact hfactorZ
    exact_mod_cast hfactorZ'
  let h := (r + 1) / 2
  have hrSplit : r + 1 = h * 2 := by
    rcases hr with ⟨j, hj⟩
    dsimp [h]
    omega
  have hpowHalf : (r ^ p + 1) / 2 = h * s := by
    rw [← hfactor, hrSplit]
    conv_lhs =>
      congr
      · rw [show h * 2 * s = 2 * (h * s) by ac_rfl]
    simp
  have hgcd : a ∣ Nat.gcd (r + 1) ((r ^ p + 1) / 2) :=
    Nat.dvd_gcd ha1 ha2
  rw [hrSplit, hpowHalf, Nat.gcd_mul_left] at hgcd
  have hcop : Nat.Coprime 2 s := Nat.coprime_two_left.mpr hsOdd
  rw [hcop.gcd_eq_one, mul_one] at hgcd
  exact hgcd

end CFSG.GorensteinWalter
