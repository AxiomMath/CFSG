module

public import CFSG.Permutation.FiveTransitive.SimpleActionEven

public section

namespace CFSG

namespace FiveTransitive.EvenInvolutionFixed

open MulAction

theorem card_mod_four
    {G X : Type*} [Group G] [Fintype X] [DecidableEq X] [MulAction G X]
    (g : G) (hg : orderOf g = 2)
    (heven : Equiv.Perm.sign (toPermHom G X g) = 1) :
    (fixedBy X g).ncard % 4 = Fintype.card X % 4 := by
  let p := toPermHom G X g
  have hp2 : p ^ 2 = 1 := by
    rw [← map_pow, show g ^ 2 = 1 from hg ▸ pow_orderOf_eq_one g, map_one]
  have hd := SimpleActionEven.four_dvd_support_of_even_involution p hp2 heven
  have hc := p.card_fixedPoints
  have hf : (fixedBy X g).ncard = Fintype.card (Function.fixedPoints p) := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    rfl
  rw [hf, hc, p.sum_cycleType]
  have hle := Finset.card_le_univ p.support
  omega

private theorem card_eq_seven
    {G X : Type*} [Group G] [Fintype X] [DecidableEq X] [MulAction G X]
    (g : G) (hg : orderOf g = 2)
    (heven : Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hlower : 5 ≤ (fixedBy X g).ncard) (hupper : (fixedBy X g).ncard ≤ 7) :
    (fixedBy X g).ncard = 7 := by
  have := card_mod_four g hg heven
  omega

theorem complementary_card_eq_two
    {G X : Type*} [Group G] [Fintype X] [DecidableEq X] [MulAction G X]
    (g : G) (hg : orderOf g = 2)
    (heven : Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hupper : (fixedBy X g).ncard ≤ 7)
    (F : Set X) (hlocal : (fixedBy X g ∩ F).ncard = 5) :
    (fixedBy X g \ F).ncard = 2 := by
  have hlower : 5 ≤ (fixedBy X g).ncard := by
    rw [← hlocal]
    exact Set.ncard_le_ncard Set.inter_subset_left
  have hc := card_eq_seven g hg heven hdegree hlower hupper
  have he : fixedBy X g \ F = fixedBy X g \ (fixedBy X g ∩ F) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [he, Set.ncard_sdiff Set.inter_subset_left, hc, hlocal]

end FiveTransitive.EvenInvolutionFixed

end CFSG
