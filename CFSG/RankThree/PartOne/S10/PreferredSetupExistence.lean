module

import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.GH74.EvenRank
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.RankThree.GroupTheory.SteinbergBMSectionTenSetup
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY

theorem isElementaryAbelian_of_isElemAbelian_prime {G : Type*} [Group G] {q : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian q E) : IsElementaryAbelian q E := by
  exact CFSG.Open.IsElemAbelian.isElementaryAbelian hE

theorem section_ten_preferred_setup_existence :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      IsKProper G → IsCharacteristicPType G 2 → twoLocalOddRank G = 3 →
      (∃ q ∈ sigmaA G, 3 < q ∧ AschVanishing G q) →
      ∃ (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A := by
  intro G _ _ _ hnonab hK hchar hrank hq
  obtain ⟨q, hqSig, hq3, hvan⟩ := hq
  have hev : evenRank G = 3 :=
    (CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank G).trans hrank
  have hsig := (aschbacher_prime_selector G).2.2.2.2.2.2.2.2.2
  have hqprime : q.Prime := (hsig q hqSig).1
  have hqrank : localRank q G = 3 := rank_three_selector_localRank_eq hev hqSig
  have hqQ : q ∈ SteinbergBM.sectionTenPrimeSet G := by
    refine ⟨hqprime, hq3, hqSig, hvan, ?_⟩
    obtain ⟨H, hH, hHr⟩ := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained q
      hqprime G (by change 0 < localRank q G; omega)
    obtain ⟨E, hEH, hEab, hEcard⟩ :=
      CFSG.RankThreeEvenClassification.Helpers.pRank_attained q hqprime H
    obtain ⟨S, hS1, hS2, hHS⟩ := hH
    have hpr : CFSG.Open.pRank q H = 3 := hHr.trans hqrank
    refine ⟨E, isElementaryAbelian_of_isElemAbelian_prime hEab, ?_, S, hS1, hS2, ?_⟩
    · rw [hEcard]
      exact congrArg (q ^ ·) hpr
    · exact hEH.trans hHS.le
  by_cases hbig : ∃ r ∈ SteinbergBM.sectionTenPrimeSet G, 7 < r
  · obtain ⟨r, hrQ, hr7⟩ := hbig
    obtain ⟨-, -, -, -, E, hE, hEc, S, hS1, hS2, hES⟩ := id hrQ
    exact ⟨r, E, inferInstance, hnonab, hK, hchar, hrank, hrQ, hE, hEc, ⟨S, hS1, hS2, hES⟩,
      fun _ => hr7⟩
  · obtain ⟨-, -, -, -, E, hE, hEc, S, hS1, hS2, hES⟩ := id hqQ
    exact ⟨q, E, inferInstance, hnonab, hK, hchar, hrank, hqQ, hE, hEc, ⟨S, hS1, hS2, hES⟩,
      fun h => absurd h hbig⟩

theorem section_ten_preferred_setup_existence_of_milestone {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G)
    (hchar : IsCharTwoType G) (hrank : evenRank G = 3)
    (hq : ∃ q ∈ sigmaA G, 3 < q ∧ AschVanishing G q) :
    ∃ (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A :=
  section_ten_preferred_setup_existence G hnonab
    (CFSG.ComponentClassification.CatalogueKProper.isKProper_iff_kProper.mpr hK)
    (CFSG.GH74.isCharTwoType_iff.mp hchar)
    ((CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank G).symm.trans hrank) hq

end CFSG.RankThree.PartOne
