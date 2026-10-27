module

public import CFSG.Permutation.FiveTransitive.A9TenQuotientNineOrbit
public import CFSG.Permutation.FiveTransitive.NineOrbitRestriction

public section

namespace CFSG

namespace FiveTransitive.A9TenQuotientFiveSupport
open MulAction

private theorem support_eq_five
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E ≤ 10)
    (B : Subgroup (Equiv.Perm E)) (tau : B →* alternatingGroup F)
    (htau : Function.Surjective tau) (b : B) (hb : orderOf b = 5) :
    (b : Equiv.Perm E).support.card = 5 := by
  obtain ⟨x,hx⟩ := A9TenQuotientNineOrbit.exists_nine_orbit hF hE B tau htau
  have hs := NineOrbitRestriction.support_le_nine hE B x hx b
  have hg : orderOf (b : Equiv.Perm E) = 5 := (Subgroup.orderOf_coe b).trans hb
  have hc : (b : Equiv.Perm E).IsCycle := Equiv.Perm.isCycle_of_prime_order
    (by rw [hg]; decide) (by rw [hg]; omega)
  exact hc.orderOf.symm.trans hg

theorem fixed_card_five
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E = 10)
    (B : Subgroup (Equiv.Perm E)) (tau : B →* alternatingGroup F)
    (htau : Function.Surjective tau) (b : B) (hb : orderOf b = 5) :
    (fixedBy E b).ncard = 5 := by
  have hs := support_eq_five hF hE.le B tau htau b hb
  change (Function.fixedPoints (b : Equiv.Perm E)).ncard = 5
  rw [← Nat.card_coe_set_eq,Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,
    (b : Equiv.Perm E).sum_cycleType,hs,← Nat.card_eq_fintype_card,hE]

end FiveTransitive.A9TenQuotientFiveSupport

end CFSG
