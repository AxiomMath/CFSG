module

public import CFSG.Permutation.FiveTransitive.Degree20SevenCycle
public import CFSG.Permutation.FiveTransitive.Degree20SupportSix

public section

namespace CFSG

namespace FiveTransitive.Degree20

open MulAction SubMulAction Subgroup

theorem alternatingGroup_le_of_nontrivial_support_le_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 20)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (hgNe : g ≠ 1) (hgsupport : g.support.card ≤ 7) :
    alternatingGroup X ≤ P := by
  classical
  let Z : Subgroup (Equiv.Perm X) :=
    Subgroup.zpowers g
  have hZnontrivial : Nontrivial Z :=
    Z.nontrivial_iff_ne_bot.mpr
      (Subgroup.zpowers_ne_bot.mpr hgNe)
  have hZcard : 1 < Nat.card Z :=
    Finite.one_lt_card_iff_nontrivial.mpr hZnontrivial
  obtain ⟨q, hq, hqdvd⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.card Z) (by omega)
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨v, hvorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := Z) q hqdvd
  obtain ⟨z, hz⟩ :=
    Subgroup.mem_zpowers_iff.mp v.prop
  let w : Equiv.Perm X := v
  have hwP : w ∈ P := by
    change (v : Equiv.Perm X) ∈ P
    rw [← hz]
    exact P.zpow_mem hg z
  have hworder : orderOf w = q := by
    calc
      orderOf w = orderOf v := Subgroup.orderOf_coe _
      _ = q := hvorder
  have hwNe : w ≠ 1 := by
    intro hw
    rw [hw, orderOf_one] at hworder
    exact hq.ne_one hworder.symm
  have hwsupport : w.support.card ≤ 7 := by
    calc
      w.support.card ≤ g.support.card := by
        change (v : Equiv.Perm X).support.card ≤
          g.support.card
        rw [← hz]
        exact Finset.card_le_card
          (Equiv.Perm.support_zpow_le g z)
      _ ≤ 7 := hgsupport
  by_cases hsmall : w.support.card ≤ 5
  · exact
      Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
        X P h5 (by omega) hwP hwNe hsmall
  rcases (show w.support.card = 6 ∨
      w.support.card = 7 by omega) with hsix | hseven
  · exact alternatingGroup_le_of_prime_order_support_six
      X P hcard h5 hwP hq hworder hsix
  · have hwprime : (orderOf w).Prime := by
      rw [hworder]
      exact hq
    obtain ⟨m, hm⟩ :=
      Equiv.Perm.cycleType_prime_order hwprime
    have hsum := w.sum_cycleType
    rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
      Nat.cast_id, hworder, hseven] at hsum
    have hqSeven : q = 7 := by
      have hqle : q ≤ 7 := by
        nlinarith [Nat.zero_le m]
      interval_cases q
      all_goals norm_num at hq
      all_goals omega
    have hmOne : m + 1 = 1 := by
      rw [hqSeven] at hsum
      omega
    have hwcycle : w.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one, hm,
        Multiset.card_replicate, hmOne]
    exact Degree20Seven.alternatingGroup_le_of_sevenCycle
      X P hcard h5 hwP hwcycle hseven

end FiveTransitive.Degree20

end CFSG
