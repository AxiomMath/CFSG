module

public import CFSG.Permutation.FiveTransitive.A9LargeAlternatingQuotient
public import CFSG.Permutation.FiveTransitive.LargePrimeCyclePrimitive
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan

public section

namespace CFSG

namespace FiveTransitive.A9TransitiveTenThirteen
open MulAction

theorem not_surjective
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hlo : 10 ≤ Nat.card E) (hhi : Nat.card E ≤ 13)
    (B : Subgroup (Equiv.Perm E)) [IsPretransitive B E]
    (tau : B →* alternatingGroup F) : ¬ Function.Surjective tau := by
  classical
  intro htau
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hdA : 7 ∣ Nat.card (alternatingGroup F) := by
    rw [nat_card_alternatingGroup,hF]; norm_num [Nat.factorial]
  have hd := hdA.trans (Subgroup.card_dvd_of_surjective htau)
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := B) 7 hd
  have hg : orderOf (u : Equiv.Perm E) = 7 := (Subgroup.orderOf_coe u).trans hu
  have hc : (u : Equiv.Perm E).IsCycle := Equiv.Perm.isCycle_of_prime_order
    (by rw [hg]; decide) (by
      have hs := Finset.card_le_univ (u : Equiv.Perm E).support
      rw [← Nat.card_eq_fintype_card] at hs
      rw [hg]
      omega)
  have hs : (u : Equiv.Perm E).support.card = 7 := hc.orderOf.symm.trans hg
  have hp := LargePrimeCyclePrimitive.isPreprimitive B u.property hc
    (by rw [hs]; decide) (by rw [hs]; omega)
  have halt := OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    hp (by decide : Nat.Prime 7) (by omega) hc hs u.property
  exact A9LargeAlternatingQuotient.not_surjective hF hlo B halt tau htau

end FiveTransitive.A9TransitiveTenThirteen

end CFSG
