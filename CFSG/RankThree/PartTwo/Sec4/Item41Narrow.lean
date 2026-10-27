module

import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeTools
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree (centerThreePrime centerThreePrime_le_center
  not_three_dvd_card_centerThreePrime isPGroup_center_quotient_centerThreePrime)

@[expose] def Item4_1LargePrime : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G →
    ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal], ¬ 3 ∣ Nat.card N → IsQuasisimple (H ⧸ N) →
      ∀ p : ℕ, p.Prime → 3 < p → p ∣ Nat.card N → localRank p (H ⧸ N) < 3

@[expose] def Item4_1ThreeCover : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SectionFourHyp X → IsQuasisimple X →
    IsPGroup 3 (Subgroup.center X) → Subgroup.center X ≠ ⊥ →
      localRank 3 (X ⧸ Subgroup.center X) ≤ 3

namespace Item41Narrow

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_subgroupOf_dvd (N H : Subgroup G) : Nat.card (N.subgroupOf H) ∣ Nat.card N := by
  rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype]
  exact Subgroup.card_dvd_of_le inf_le_left

theorem localRank_section_le (H : Subgroup G) (N : Subgroup H) [N.Normal] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpN : ¬ p ∣ Nat.card N) : localRank p (H ⧸ N) ≤ localRank p G :=
  (CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 N hpN).trans (localRank_subgroup_le hp H)

theorem sectionFourHyp_section (h1 : Item4_1LargePrime) (hG : SectionFourHyp G)
    (H : Subgroup G) (N : Subgroup H) [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    (hq : IsQuasisimple (H ⧸ N)) : SectionFourHyp (H ⧸ N) := by
  have hlt : ∀ p : ℕ, p.Prime → 3 < p → localRank p (H ⧸ N) < 3 := fun p hp hp3 => by
    by_cases hpN : p ∣ Nat.card N
    · exact h1 G hG H N hN hq p hp hp3 hpN
    · exact (localRank_section_le H N hp (by omega) hpN).trans_lt (hG.localRank_lt p hp hp3)
  refine ⟨CFSG.SectionRank.K_group_section_closure_inCatalog hG.kGroup H N (MulEquiv.refl _),
    Census.evenRank_le_of_localRank_le fun p hp hp2 => ?_, hlt⟩
  rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with rfl | hp3
  · exact (localRank_section_le H N Nat.prime_three (by norm_num) hN).trans
      ((OddKernel.localRank_le_evenRank Nat.prime_three (by norm_num)).trans hG.evenRank_le)
  · exact (hlt p hp hp3).le.trans (by norm_num)

noncomputable def quotientTopEquiv (K : Subgroup G) [K.Normal] :
    (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤ ≃* G ⧸ K :=
  QuotientGroup.congr _ _ Subgroup.topEquiv (by
    ext x
    simp [Subgroup.mem_map, Subgroup.mem_subgroupOf])

theorem sectionFourHyp_quotient (h1 : Item4_1LargePrime) (hG : SectionFourHyp G)
    (K : Subgroup G) [K.Normal] (hK : ¬ 3 ∣ Nat.card K) (hq : IsQuasisimple (G ⧸ K)) :
    SectionFourHyp (G ⧸ K) :=
  Census.sectionFourHyp_of_mulEquiv (quotientTopEquiv K)
    (sectionFourHyp_section h1 hG ⊤ _ (fun h => hK (h.trans (card_subgroupOf_dvd K ⊤)))
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (quotientTopEquiv K).symm hq))

theorem sectionFourHyp_thetaQuotient (h1 : Item4_1LargePrime) (hG : SectionFourHyp G)
    {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) :
    SectionFourHyp (L ⧸ aschbacherSolvableCore 3 L) :=
  sectionFourHyp_section h1 hG L _ three_not_dvd_card_aschbacherSolvableCore hL.2.2

variable {X : Type} [Group X] [Finite X]

theorem localRank_quotient_center_le (hZ : IsPGroup 3 (Subgroup.center X)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) : localRank p (X ⧸ Subgroup.center X) ≤ localRank p X := by
  refine CFSG.RankThree.Classical2.localRank_quotient_le hp (by omega) _ fun hpZ => ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
  rw [hk] at hpZ
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hpZ)
  omega

theorem sectionFourHyp_quotient_center_of_isPGroup (h2 : Item4_1ThreeCover)
    (hX : SectionFourHyp X) (hq : IsQuasisimple X) (hZ : IsPGroup 3 (Subgroup.center X)) :
    SectionFourHyp (X ⧸ Subgroup.center X) := by
  have hlt : ∀ p : ℕ, p.Prime → 3 < p → localRank p (X ⧸ Subgroup.center X) < 3 :=
    fun p hp hp3 => (localRank_quotient_center_le hZ hp hp3).trans_lt (hX.localRank_lt p hp hp3)
  have h3 : localRank 3 (X ⧸ Subgroup.center X) ≤ 3 := by
    by_cases hZ1 : Subgroup.center X = ⊥
    · rw [Census.localRank_eq_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot) Nat.prime_three]
      exact (OddKernel.localRank_le_evenRank Nat.prime_three (by norm_num)).trans hX.evenRank_le
    · exact h2 X hX hq hZ hZ1
  refine ⟨CFSG.SectionRank.K_group_section_closure_inCatalog hX.kGroup ⊤ _
      (Census.quotientCenterEquiv X), Census.evenRank_le_of_localRank_le fun p hp hp2 => ?_, hlt⟩
  rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with rfl | hp3
  · exact h3
  · exact (hlt p hp hp3).le.trans (by norm_num)

theorem sectionFourHyp_quotient_center (h1 : Item4_1LargePrime) (h2 : Item4_1ThreeCover)
    (hX : SectionFourHyp X) (hq : IsQuasisimple X) : SectionFourHyp (X ⧸ Subgroup.center X) := by
  obtain ⟨hq', -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hq (centerThreePrime X)
    centerThreePrime_le_center
  have hY := sectionFourHyp_quotient h1 hX (centerThreePrime X)
    not_three_dvd_card_centerThreePrime hq'
  let e : (X ⧸ centerThreePrime X) ⧸ Subgroup.center (X ⧸ centerThreePrime X) ≃*
      X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientQuotientEquivQuotient _ _ centerThreePrime_le_center)
  exact Census.sectionFourHyp_of_mulEquiv e (sectionFourHyp_quotient_center_of_isPGroup h2 hY hq'
    (isPGroup_center_quotient_centerThreePrime hq))

end Item41Narrow

end CFSG.RankThree.PartTwo.Sec4
