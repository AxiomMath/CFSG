module

import CFSG.RankThree.PartOne.S10.CentralCoverLocalRankFourObstruction
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.RankThree.Classical.EvenSurvivingScalarRank
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.RankThreeEven

namespace SourceSixThirteen

theorem le_localRank_iff_exists {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : 1 ≤ k) :
    k ≤ localRank p G ↔ ∃ U : Subgroup G, IsPGroup 2 U ∧ U ≠ ⊥ ∧
      ∃ E : Subgroup G, E ≤ Subgroup.normalizer (U : Set G) ∧ IsElementaryAbelian p E ∧
        Nat.card E = p ^ k := by
  constructor
  · intro hle
    by_contra hno
    push Not at hno
    have hlt : localRank p G ≤ k - 1 := by
      refine csSup_le' ?_
      rintro m ⟨H', ⟨S, hS0, hS2, rfl⟩, rfl⟩
      by_contra hm
      push Not at hm
      obtain ⟨E, hEN, hE, hEc⟩ := (Planes.le_pRank_iff hp
        (Subgroup.normalizer (S : Set G)) k).1 (by omega)
      exact hno S hS2 hS0 E hEN hE hEc
    omega
  · rintro ⟨U, hU2, hU0, E, hEN, hE, hEc⟩
    have h4 : k ≤ CFSG.Assembly.pRank p (Subgroup.normalizer (U : Set G)) :=
      (Planes.le_pRank_iff hp _ k).2 ⟨E, hEN, hE, hEc⟩
    have h5 := CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt
      (⟨U, hU0, hU2, rfl⟩ : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (U : Set G)))
    omega

theorem three_lt_localRank_iff_exists_elementary_abelian_normalizer {V : Type*} [Group V]
    [Finite V] {p : ℕ} (hp : p.Prime) :
    3 < localRank p V ↔ ∃ U : Subgroup V, IsPGroup 2 U ∧ U ≠ ⊥ ∧
      ∃ E : Subgroup V, E ≤ Subgroup.normalizer (U : Set V) ∧ IsElementaryAbelian p E ∧
        Nat.card E = p ^ 4 :=
  le_localRank_iff_exists hp (by norm_num)

theorem mem_of_pow_five_mem_of_coprime {G : Type*} [Group G] {N : Subgroup G} {g : G}
    (hg : g ^ 5 ∈ N) (hc : Nat.Coprime 5 (orderOf g)) : g ∈ N := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hc
  rw [← hm]
  exact N.pow_mem hg m

theorem localRank_le_of_forall_pow_five_mem {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    (hN : ∀ g : G, g ^ 5 ∈ N) {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    localRank p G ≤ localRank p N := by
  rcases Nat.eq_zero_or_pos (localRank p G) with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  obtain ⟨U, hU2, hU0, E, hEN, hE, hEc⟩ := (le_localRank_iff_exists hp hpos).1 le_rfl
  have hUN : U ≤ N := by
    intro u hu
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hU2 ⟨u, hu⟩
    refine mem_of_pow_five_mem_of_coprime (hN u) ?_
    have : orderOf u = 2 ^ k := by rwa [← Subgroup.orderOf_mk u hu]
    rw [this]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hEN' : E ≤ N := by
    intro e he
    have := hE
    have hdvd : orderOf e ∣ p :=
      orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian e he)
    refine mem_of_pow_five_mem_of_coprime (hN e) ?_
    exact Nat.Coprime.coprime_dvd_right hdvd
      ((Nat.coprime_primes Nat.prime_five hp).mpr (Ne.symm hp5))
  refine (le_localRank_iff_exists hp hpos).2 ⟨U.subgroupOf N, ?_, ?_, E.subgroupOf N, ?_, ?_, ?_⟩
  · exact hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUN).symm
  · intro hbot
    apply hU0
    have := Subgroup.map_subgroupOf_eq_of_le hUN
    rw [hbot, Subgroup.map_bot] at this
    exact this.symm
  · intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have := Subgroup.mem_normalizer_iff.mp (hEN he) (u : G)
    exact this
  · exact CentralCoverObstruction.isElementaryAbelian_of_mulEquiv_of_isElementaryAbelian
      (Subgroup.subgroupOfEquivOfLe hEN').symm hE
  · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN').toEquiv).trans hEc

theorem localRank_range_le_of_not_dvd_card_ker {G G' : Type} [Group G] [Group G'] [Finite G]
    [Finite G'] (f : G →* G') {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hker : ¬ p ∣ Nat.card f.ker) :
    localRank p f.range ≤ localRank p G := by
  have e : localRank p (G ⧸ f.ker) = localRank p f.range :=
    CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
      (QuotientGroup.quotientKerEquivRange f) hp
  rw [← e]
  exact CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 f.ker hker

end SourceSixThirteen

end CFSG.RankThree.PartOne
