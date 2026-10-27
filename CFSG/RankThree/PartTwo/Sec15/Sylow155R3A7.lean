module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.ComponentClassification

private theorem exists_mem_dvd_of_prime_dvd_lcm {q : ℕ} (hq : q.Prime) (s : Multiset ℕ)
    (h : q ∣ s.lcm) : ∃ a ∈ s, q ∣ a := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.lcm_zero] at h
    exact absurd (Nat.dvd_one.mp h) hq.ne_one
  | cons a s ih =>
    rw [Multiset.lcm_cons, lcm_eq_nat_lcm] at h
    rcases hq.dvd_lcm.mp h with ha | hs
    · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
    · obtain ⟨b, hb, hqb⟩ := ih hs
      exact ⟨b, Multiset.mem_cons_of_mem hb, hqb⟩

private theorem false_of_commute_of_coprime_six {s t : Equiv.Perm (Fin 7)} (hs3 : s ^ 3 = 1)
    (hs1 : s ≠ 1) {m : ℕ} (ht : t ^ m = 1) (hm : Nat.Coprime m 6) (ht1 : t ≠ 1)
    (hst : Commute s t) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hos : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hn6 : Nat.Coprime (orderOf t) 6 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one ht) hm
  have hn1 : orderOf t ≠ 1 := fun h => ht1 (orderOf_eq_one_iff.mp h)
  have hpp : (orderOf t).minFac.Prime := Nat.minFac_prime hn1
  have hpn : (orderOf t).minFac ∣ orderOf t := Nat.minFac_dvd _
  have hp6 : Nat.Coprime (orderOf t).minFac 6 := Nat.Coprime.coprime_dvd_left hpn hn6
  have hp5 : 5 ≤ (orderOf t).minFac := by
    by_contra hlt
    have h2 := hpp.two_le
    generalize (orderOf t).minFac = p at hpp hp6 hlt h2
    interval_cases p
    · exact absurd hp6 (by decide)
    · exact absurd hp6 (by decide)
    · exact absurd hpp (by decide)
  have hp3 : Nat.Coprime 3 (orderOf t).minFac :=
    (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hp6).symm
  have hcop : (orderOf s).Coprime (orderOf t) := by
    rw [hos]
    exact (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hn6).symm
  have hw : orderOf (s * t) = 3 * orderOf t := by
    rw [hst.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hos]
  have h3w : 3 ∣ (s * t).cycleType.lcm := by
    rw [Equiv.Perm.lcm_cycleType, hw]
    exact dvd_mul_right 3 _
  have hpw : (orderOf t).minFac ∣ (s * t).cycleType.lcm := by
    rw [Equiv.Perm.lcm_cycleType, hw]
    exact Dvd.dvd.mul_left hpn 3
  obtain ⟨a, ha, h3a⟩ := exists_mem_dvd_of_prime_dvd_lcm Nat.prime_three _ h3w
  obtain ⟨b, hb, hpb⟩ := exists_mem_dvd_of_prime_dvd_lcm hpp _ hpw
  have ha2 := Equiv.Perm.two_le_of_mem_cycleType ha
  have hb2 := Equiv.Perm.two_le_of_mem_cycleType hb
  have ha3 : 3 ≤ a := Nat.le_of_dvd (by omega) h3a
  have hb5 : 5 ≤ b := hp5.trans (Nat.le_of_dvd (by omega) hpb)
  have hsum := Equiv.Perm.sum_cycleType_le (s * t)
  rw [Fintype.card_fin] at hsum
  by_cases hab : a = b
  · subst hab
    have h15 : 3 * (orderOf t).minFac ∣ a := Nat.Coprime.mul_dvd_of_dvd_of_dvd hp3 h3a hpb
    have hle := Nat.le_of_dvd (by omega) h15
    have hale := Multiset.le_sum_of_mem ha
    omega
  · obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem ha
    have hbu : b ∈ u := by
      have hb' : b ∈ a ::ₘ u := hu ▸ hb
      rcases Multiset.mem_cons.mp hb' with h | h
      · exact absurd h.symm hab
      · exact h
    rw [hu, Multiset.sum_cons] at hsum
    have hble := Multiset.le_sum_of_mem hbu
    omega

theorem res3NoDatumA7_holds : Res3NoDatumA7 := by
  rintro J _ _ _ hq ⟨e⟩ c g V U hd
  haveI : Group.IsPerfect J := hq.1
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  let ε : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective _ hbij
  let Φ : MulAut J →* Equiv.Perm (Fin 7) :=
    ε.symm.toMonoidHom.comp
      ((MulAut.congr e).toMonoidHom.comp (PerfectAutomorphisms.centerQuotientHom J))
  have hΦ : Function.Injective Φ :=
    ε.symm.injective.comp
      ((MulAut.congr e).injective.comp (PerfectAutomorphisms.centerQuotientHom_injective J))
  refine false_of_commute_of_coprime_six (s := Φ c) (t := Φ g) (m := orderOf g) ?_ ?_ ?_
    hd.coprime_six ?_ (hd.comm.map Φ)
  · rw [← map_pow, hd.c_pow, map_one]
  · exact fun h => hd.c_ne_one (hΦ (h.trans (map_one Φ).symm))
  · rw [← map_pow, pow_orderOf_eq_one, map_one]
  · exact fun h => hd.g_ne_one (hΦ (h.trans (map_one Φ).symm))

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
