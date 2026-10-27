module

public import CFSG.RankThree.PartOne.K133.KillRank

public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.GorensteinWalter CFSG.RankThree.PartOne.K133
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem noRankThree_of_isoLie_suzuki
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hne : ∃ a b : X, a * b ≠ b * a) {m : ℕ}
    (hiso : IsoLie X (.suzuki m)) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : NoRankThree p X := by
  have : Fact p.Prime := ⟨hp⟩
  have hmodel := CTP.suzukiModel_of_isoLie m hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have e' : X ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have hsyl := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    a ha hF' e'
  have hcyc : IsCyclic (Outer (CFSG.Blueprint.suzukiGroup a F)) :=
    (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hF').1
  refine noRankThree_of_rank_le_one hp (center_eq_bot_of_simple_nonabelian hne) ?_ ?_
  · intro A hA
    have hodd : Odd (Nat.card A) := by
      have : IsPGroup p A := IsElementaryAbelian.isPGroup p A
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 this
      rw [hk]
      exact (hp.eq_two_or_odd'.resolve_left (by omega)).pow
    have hc := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.odd_commutative_subgroup_cyclic
      A hodd inferInstance hsyl
    have : IsCyclic A := hc
    have hexp : Monoid.exponent ↥A ∣ p := IsElementaryAbelian.exponent_dvd_p p _
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd hp.pos hexp
  · intro B hB
    have heq : Outer X ≃* Outer (CFSG.Blueprint.suzukiGroup a F) := equivalence e
    have : IsCyclic (Outer X) := isCyclic_of_surjective heq.symm.toMonoidHom heq.symm.surjective
    exact card_le_of_isCyclic_elemAb hp B hB

theorem noRankThree_of_isoLie_tits
    {X : Type} [Group X] [Finite X] (hX : IsoLie X .tits) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    NoRankThree p X := by
  rintro ⟨E, hE, hc⟩
  obtain ⟨hT, -, hO, -⟩ :=
    CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound X 2 1
      (CTP.reeTitsModel_tits hX)
  have hdvd : Nat.card (MulAut X) ∣ 2 * 17971200 := by
    have := CFSG.RankThree.ReeTitsAut.card_mulAut_dvd X
    rwa [hO, hT] at this
  have h3 : p ^ 3 ∣ 2 * 17971200 := by
    rw [← hc]
    exact (Subgroup.card_subgroup_dvd_card E).trans hdvd
  by_cases hp5 : p = 5
  · subst hp5
    norm_num at h3
  · exact CTP.not_sq_dvd_tits_aut hp h5 hp5
      ((pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans h3)

end CFSG.RankThree.PartOne.K159F
