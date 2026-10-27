module

public import CFSG.Permutation.FiveTransitive.Degree67TwoKernelMoments
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoKernelBound
open MulAction

theorem card_le_sixteen
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hG : IsPGroup 2 G) (hX : Fintype.card X = 67)
    (s : Finset X) (hs : s.card = 23) (hfixed : ∀ g : G, ∀ x ∈ s, g • x = x)
    (horbit : ∀ x : X, Nat.card (orbit G x) ≤ 4)
    (hbound : ∀ g : G, g ≠ 1 → Nat.card (fixedBy X g) ≤ 33) : Nat.card G ≤ 16 := by
  classical
  let _ : Fintype G := Fintype.ofFinite _
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨hlow,hupper⟩ := Degree67TwoKernelFirstMoment.sum_bounds hX s hs hfixed horbit hbound
  have hb : Nat.card G ≤ 34 := by omega
  have hn := Degree67TwoKernelMoments.card_ne_thirty_two hX s hs hfixed horbit hbound
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hG
  have he4 : e ≤ 4 := by
    by_contra hnot
    by_cases he5 : e = 5
    · exact hn (by rw [he,he5]; norm_num)
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ e)
    rw [he] at hb
    norm_num at hp
    omega
  rw [he]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) he4

end FiveTransitive.Degree67TwoKernelBound

end CFSG
