module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.TwoGroupSmallCard

theorem two_or_four {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hG : IsPGroup 2 G) (hle : Nat.card G ≤ 4) : Nat.card G = 2 ∨ Nat.card G = 4 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hG
  have hpos : 1 < Nat.card G := Finite.one_lt_card
  by_cases hkle : k ≤ 2
  · interval_cases k <;> norm_num at hk <;> omega
  · have h8 : 8 ∣ Nat.card G := by rw [hk]; exact Nat.pow_dvd_pow 2 (by omega : 3 ≤ k)
    have := Nat.le_of_dvd (by omega : 0 < Nat.card G) h8
    omega

end FiveTransitive.TwoGroupSmallCard

end CFSG
