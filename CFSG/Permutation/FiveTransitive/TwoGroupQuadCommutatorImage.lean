module

public import CFSG.Permutation.FiveTransitive.TwoGroupQuadCommutatorCard
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG

namespace FiveTransitive.TwoGroupQuadCommutatorImage

theorem card_le_eight
    {Y : Type*} [Finite Y] (Q : Subgroup (Equiv.Perm Y))
    (hY : Nat.card Y ≤ 4) (hQ : IsPGroup 2 Q) : Nat.card Q ≤ 8 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hd : Nat.card Q ∣ 24 := by
    have h := Subgroup.card_subgroup_dvd_card Q
    rw [Nat.card_perm] at h
    exact h.trans (by simpa [Nat.factorial] using Nat.factorial_dvd_factorial hY)
  obtain ⟨e,he⟩ := hQ.exists_card_eq
  have he3 : e ≤ 3 := by
    by_contra hn
    have h16 : 2 ^ 4 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 2 (by omega : 4 ≤ e)
    have hh := h16.trans hd
    norm_num at hh
  rw [he]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) he3

theorem commutator_card_le_two
    {Y : Type*} [Finite Y] (Q : Subgroup (Equiv.Perm Y))
    (hY : Nat.card Y ≤ 4) (hQ : IsPGroup 2 Q) : Nat.card (commutator Q) ≤ 2 := by
  exact TwoGroupQuadCommutatorCard.commutator_card_le_two hQ (card_le_eight Q hY hQ)

private theorem map_commutator_eq_image_derived
    {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (commutator G).map f = (commutator f.range).map f.range.subtype := by
  rw [map_commutator_eq,map_commutator_eq,Subgroup.range_subtype]

theorem map_commutator_card_le_two
    {G Y : Type*} [Group G] [Finite Y] (hG : IsPGroup 2 G)
    (f : G →* Equiv.Perm Y) (hY : Nat.card Y ≤ 4) :
    Nat.card ((commutator G).map f) ≤ 2 := by
  rw [map_commutator_eq_image_derived,Subgroup.card_map_of_injective f.range.subtype_injective]
  exact commutator_card_le_two f.range hY (hG.of_surjective f.rangeRestrict f.rangeRestrict_surjective)

end FiveTransitive.TwoGroupQuadCommutatorImage

end CFSG
