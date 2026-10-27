module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.DerivedTwoLift

theorem exists_two_element
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (d : H) (hd : d ∈ (commutator G).map f) (hd2 : orderOf d = 2) :
    ∃ y : G, y ∈ commutator G ∧ f y = d ∧ IsPGroup 2 (Subgroup.zpowers y) := by
  obtain ⟨g, hg, hfg⟩ := hd
  obtain ⟨k, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd
    (Nat.ne_of_gt (orderOf_pos g))
  have hm0 : m ≠ 0 := by obtain ⟨a, ha⟩ := hm; omega
  have hmdvd : m ∣ orderOf g := ⟨2 ^ k, by rw [he, Nat.mul_comm]⟩
  have ho : orderOf (g ^ m) = 2 ^ k := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, he]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  refine ⟨g ^ m, (commutator G).pow_mem hg m, ?_, ?_⟩
  · rw [map_pow, hfg, ← pow_mod_orderOf, hd2, Nat.odd_iff.mp hm, pow_one]
  · exact IsPGroup.of_card (by rw [Nat.card_zpowers, ho])

end FiveTransitive.DerivedTwoLift

end CFSG
