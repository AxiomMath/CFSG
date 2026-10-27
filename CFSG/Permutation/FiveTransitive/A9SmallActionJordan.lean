module

public import CFSG.Permutation.FiveTransitive.LargePrimeCyclePrimitive
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan
public import Mathlib.Tactic.NormNum.NatFactorial

public section

namespace CFSG

namespace FiveTransitive.A9SmallActionJordan
open MulAction

theorem excluded
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (J : Subgroup (Equiv.Perm Y)) [IsPretransitive J Y]
    (hY : Nat.card Y = 10 ∨ Nat.card Y = 12) (hJ : Nat.card J = 181440) : False := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hd : 7 ∣ Nat.card J := by rw [hJ]; norm_num
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := J) 7 hd
  have hg : orderOf (u : Equiv.Perm Y) = 7 := (Subgroup.orderOf_coe u).trans hu
  have hc : (u : Equiv.Perm Y).IsCycle := Equiv.Perm.isCycle_of_prime_order
    (by rw [hg]; decide) (by
      have hs := Finset.card_le_univ (u : Equiv.Perm Y).support
      rw [← Nat.card_eq_fintype_card] at hs
      rw [hg]
      omega)
  have hs : (u : Equiv.Perm Y).support.card = 7 := hc.orderOf.symm.trans hg
  have hp := LargePrimeCyclePrimitive.isPreprimitive J u.property hc
    (by rw [hs]; decide) (by rw [hs]; omega)
  have halt := OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    hp (by decide : Nat.Prime 7) (by omega) hc hs u.property
  let _ : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hd := Subgroup.card_dvd_of_le halt
  rw [nat_card_alternatingGroup,hJ] at hd
  rcases hY with hY | hY <;> rw [hY] at hd <;> norm_num [Nat.factorial] at hd

end FiveTransitive.A9SmallActionJordan

end CFSG
