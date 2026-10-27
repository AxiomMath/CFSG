module

public import CFSG.Permutation.FiveTransitive.HighDegreeHalfSupport
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan

public section

namespace CFSG

namespace FiveTransitive.SupportThirteenClosure

open Equiv MulAction

private theorem alternatingGroup_le_of_nontrivial_support_le_thirteen
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (hn : 28 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    {g : Perm X} (hg : g ∈ P) (hne : g ≠ 1) (hsmall : g.support.card ≤ 13) :
    alternatingGroup X ≤ P := by
  classical
  let Z : Subgroup (Perm X) := Subgroup.zpowers g
  have hZnontrivial : Nontrivial Z :=
    Z.nontrivial_iff_ne_bot.mpr (Subgroup.zpowers_ne_bot.mpr hne)
  have hZcard : 1 < Nat.card Z := Finite.one_lt_card_iff_nontrivial.mpr hZnontrivial
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd (n := Nat.card Z) (by omega)
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨v, hvorder⟩ := exists_prime_orderOf_dvd_card' (G := Z) p hpdiv
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp v.prop
  let w : Perm X := v
  have hwP : w ∈ P := by
    change (v : Perm X) ∈ P
    rw [← hz]
    exact P.zpow_mem hg z
  have hworder : orderOf w = p := (Subgroup.orderOf_coe v).trans hvorder
  have hwne : w ≠ 1 := by
    intro hw
    rw [hw, orderOf_one] at hworder
    exact hp.ne_one hworder.symm
  have hwsmall : w.support.card ≤ 13 := by
    calc
      w.support.card ≤ g.support.card := by
        change (v : Perm X).support.card ≤ g.support.card
        rw [← hz]
        exact Finset.card_le_card (Perm.support_zpow_le g z)
      _ ≤ 13 := hsmall
  by_cases hwtwelve : w.support.card ≤ 12
  · exact HighDegreeHalfSupport.alternatingGroup_le_of_nontrivial_support_le_twelve
      P hn h5 hwP hwne hwtwelve
  have hwthirteen : w.support.card = 13 := by omega
  have hpdiv13 : p ∣ 13 := by
    simpa only [hwthirteen] using PrimeSupportConstraints.prime_dvd_support_card hp hworder
  have hp13 : p = 13 := by
    rcases (Nat.dvd_prime (by norm_num)).mp hpdiv13 with hone | hthirteen
    · exact (hp.ne_one hone).elim
    · exact hthirteen
  have hwprime : (orderOf w).Prime := by rwa [hworder]
  have hwcycle : w.IsCycle := Perm.isCycle_of_prime_order hwprime (by
    rw [hworder, hp13, hwthirteen]
    norm_num)
  let _ : MulAction.IsMultiplyPretransitive P X 5 := h5
  have h2 : MulAction.IsMultiplyPretransitive P X 2 :=
    MulAction.isMultiplyPretransitive_of_le (G := P) (α := X) (m := 2) (n := 5)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using (show 5 ≤ Fintype.card X by omega))
  exact OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    (MulAction.isPreprimitive_of_is_two_pretransitive h2) (by norm_num : Nat.Prime 13)
    (by rw [Nat.card_eq_fintype_card]; omega) hwcycle hwthirteen hwP

theorem fourteen_le_support
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (hn : 28 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (hnotAlt : ¬ alternatingGroup X ≤ P)
    {g : Perm X} (hg : g ∈ P) (hne : g ≠ 1) : 14 ≤ g.support.card := by
  by_contra hlt
  exact hnotAlt (alternatingGroup_le_of_nontrivial_support_le_thirteen P hn h5 hg hne (by omega))

end FiveTransitive.SupportThirteenClosure

end CFSG
