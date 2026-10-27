module

public import CFSG.Permutation.FiveTransitive.SevenCycleGeneric

public section

namespace CFSG

namespace FiveTransitive.PrimeSupportConstraints

theorem prime_dvd_support_card
    {X : Type} [Fintype X] [DecidableEq X]
    {g : Equiv.Perm X} {p : ℕ}
    (hp : p.Prime) (hgOrder : orderOf g = p) :
    p ∣ g.support.card := by
  have hgPrime : (orderOf g).Prime := by
    rw [hgOrder]
    exact hp
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgPrime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgOrder] at hsum
  exact ⟨m + 1, by simpa [mul_comm] using hsum.symm⟩

theorem alternatingGroup_le_of_nontrivial_support_le_seven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : 15 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
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
  obtain ⟨p, hp, hpdiv⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.card Z) (by omega)
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨v, hvorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := Z) p hpdiv
  obtain ⟨z, hz⟩ :=
    Subgroup.mem_zpowers_iff.mp v.prop
  let w : Equiv.Perm X := v
  have hwP : w ∈ P := by
    change (v : Equiv.Perm X) ∈ P
    rw [← hz]
    exact P.zpow_mem hg z
  have hworder : orderOf w = p := by
    calc
      orderOf w = orderOf v := Subgroup.orderOf_coe _
      _ = p := hvorder
  have hwNe : w ≠ 1 := by
    intro hw
    rw [hw, orderOf_one] at hworder
    exact hp.ne_one hworder.symm
  have hwsupport : w.support.card ≤ 7 := by
    calc
      w.support.card ≤ g.support.card := by
        change (v : Equiv.Perm X).support.card ≤
          g.support.card
        rw [← hz]
        exact Finset.card_le_card
          (Equiv.Perm.support_zpow_le g z)
      _ ≤ 7 := hgsupport
  by_cases hsmall : w.support.card ≤ 6
  · exact
      SmallSupportGeneric.alternatingGroup_le_of_nontrivial_support_le_six
        P (by omega) h5 hwP hwNe hsmall
  · have hsupportSeven : w.support.card = 7 := by
      omega
    have hpDvdSeven : p ∣ 7 := by
      simpa only [hsupportSeven] using
        prime_dvd_support_card hp hworder
    have hpSeven : p = 7 := by
      rcases (Nat.dvd_prime (by norm_num)).mp hpDvdSeven with
        hpOne | hpSeven
      · exact (hp.ne_one hpOne).elim
      · exact hpSeven
    have hwPrime : (orderOf w).Prime := by
      rw [hworder]
      exact hp
    have hwCycle : w.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order hwPrime (by
        rw [hworder, hpSeven, hsupportSeven]
        norm_num)
    exact
      SevenCycleGeneric.alternatingGroup_le_of_sevenCycle_mem
        P hcard h5 hwP hwCycle hsupportSeven

end FiveTransitive.PrimeSupportConstraints

end CFSG
