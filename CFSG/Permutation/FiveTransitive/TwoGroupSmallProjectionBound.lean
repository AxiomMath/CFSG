module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG

namespace FiveTransitive.TwoGroupSmallProjectionBound

private theorem commutator_range_card_le
    {G K : Type*} [Group G] [Group K] [Finite G] (f : G →* K) :
    Nat.card (commutator f.range) ≤ Nat.card (commutator G) := by
  have he : (commutator G).map f.rangeRestrict = commutator f.range := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr f.rangeRestrict_surjective]
    rfl
  have hd := (commutator G).card_map_dvd f.rangeRestrict
  rw [he] at hd
  exact Nat.le_of_dvd Nat.card_pos hd

theorem card_le
    {G K : Type*} [Group G] [Group K] [Finite G]
    (hG : IsPGroup 2 G) (f : G →* K)
    (hker : Nat.card f.ker ≤ 16) (hrange : Nat.card f.range ≤ 8192)
    (hderived : Nat.card (commutator G) ≤ 8)
    (hfull : Nat.card f.range = 8192 → 16 ≤ Nat.card (commutator f.range)) :
    Nat.card G ≤ 65536 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  by_contra hn
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hG
  have he17 : 17 ≤ e := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : e ≤ 16)
    norm_num at hp
    rw [he] at hn
    omega
  have hlow : 131072 ≤ Nat.card G := by
    rw [he]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) he17
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hc
  have hmul := Nat.mul_le_mul_right (Nat.card f.range) hker
  have hfullcard : Nat.card f.range = 8192 := by nlinarith
  have hd := (commutator_range_card_le f).trans hderived
  have hl := hfull hfullcard
  omega

end FiveTransitive.TwoGroupSmallProjectionBound

end CFSG
