module

public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeOrbitImage

public section

namespace CFSG

namespace FiveTransitive.Degree72LargePrimeOrbitSize
open MulAction

theorem card_le_prime
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (p : ℕ) (hp : p.Prime) (hG : IsPGroup p G) (hn : Nat.card X < p ^ 2)
    (x : X) : Nat.card (orbit G x) ≤ p := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨e,he⟩ := hG.card_orbit x
  have hb := Nat.card_le_card_of_injective (fun y : orbit G x => y.val) Subtype.val_injective
  have he1 : e ≤ 1 := by
    by_contra hh
    have hpow := Nat.pow_le_pow_right hp.pos (by omega : 2 ≤ e)
    rw [← he] at hpow
    omega
  rw [he]
  interval_cases e
  · simpa using hp.one_le
  · simp

theorem card_eq_prime
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (p : ℕ) (hp : p.Prime) (hG : IsPGroup p G) (hn : Nat.card X < p ^ 2)
    (x : X) (hx : x ∉ fixedPoints G X) : Nat.card (orbit G x) = p := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  let _ : Fact p.Prime := ⟨hp⟩
  have hb := card_le_prime p hp hG hn x
  obtain ⟨e,he⟩ := hG.card_orbit x
  have hne : e ≠ 0 := by
    intro he0
    exact hx (mem_fixedPoints_iff_card_orbit_eq_one.mpr (by
      rw [← Nat.card_eq_fintype_card,he,he0,pow_zero]))
  have hl := Nat.pow_le_pow_right hp.pos (by omega : 1 ≤ e)
  rw [pow_one,← he] at hl
  omega

end FiveTransitive.Degree72LargePrimeOrbitSize

end CFSG
