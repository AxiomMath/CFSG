module

public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Cardinality of a normal p-complement

A normal subgroup of order prime to `p` whose quotient is a `p`-group is
exactly the `p`-free part of the ambient group order.
-/

namespace CFSG.GorensteinWalter

/-- The order of a normal `p`-complement is the maximal factor of the ambient
order not divisible by `p`. -/
public theorem normalPComplement_card_eq_divMaxPow
    {G : Type*} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (N : Subgroup G) [N.Normal]
    (hNcop : Nat.Coprime p (Nat.card N))
    (hquotp : IsPGroup p (G ⧸ N)) :
    Nat.card N = (Nat.card G).divMaxPow p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hquotp.exists_card_eq
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [ha] at hcard
  rw [hcard, Nat.divMaxPow_base_pow_mul hp.ne_zero]
  have hndiv : ¬ p ∣ Nat.card N := hp.coprime_iff_not_dvd.mp hNcop
  have hv : padicValNat p (Nat.card N) = 0 :=
    padicValNat.eq_zero_of_not_dvd hndiv
  have hdecomp := Nat.pow_padicValNat_mul_divMaxPow p (Nat.card N)
  rw [hv] at hdecomp
  simpa using hdecomp.symm

end CFSG.GorensteinWalter
