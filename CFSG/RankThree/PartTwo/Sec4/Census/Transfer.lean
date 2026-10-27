module

import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.RankThree.Coprime.EvenCenterSectionCover
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (localRank)

theorem evenRank_le_of_localRank_le {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → localRank p Y ≤ m) : CFSG.Assembly.evenRank Y ≤ m := by
  apply csSup_le'
  rintro _ ⟨p, H, hp, hp2, hH, rfl⟩
  exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank p hp H hH).trans
    (h p hp hp2)

theorem sectionFourHyp_of_mulEquiv {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (e : X ≃* Y) (h : SectionFourHyp X) : SectionFourHyp Y where
  kGroup := CFSG.SectionRank.K_group_section_closure_inCatalog h.kGroup ⊤ ⊥
    (QuotientGroup.quotientBot.trans (Subgroup.topEquiv.trans e))
  evenRank_le :=
    (CFSG.RankThree.PartOne.Census3.evenRank_le_of_mulEquiv e.symm).trans h.evenRank_le
  localRank_lt p hp hp3 := by
    rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp]
    exact h.localRank_lt p hp hp3

theorem sectionFourHyp_of_section (h41 : Item4_1) {G : Type} [Group G] [Finite G]
    (hG : SectionFourHyp G) (H : Subgroup G) (N : Subgroup H) [N.Normal]
    (hq : IsQuasisimple (H ⧸ N)) : SectionFourHyp (H ⧸ N) := by
  obtain ⟨⟨hlt, h3⟩, -⟩ := h41 G hG H N (CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hq)
  refine ⟨CFSG.SectionRank.K_group_section_closure_inCatalog hG.kGroup H N (MulEquiv.refl _),
    evenRank_le_of_localRank_le fun p hp hp2 => ?_, hlt⟩
  by_cases hp3 : p = 3
  · subst hp3
    exact h3 hq
  · have : 3 < p := by
      have := hp.two_le
      rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 4 < p by omega) with h | h | h | h
      · exact absurd h hp2
      · exact absurd h hp3
      · exact absurd (h ▸ hp) (by norm_num)
      · omega
    exact (hlt p hp this).le.trans (by norm_num)

noncomputable def quotientCenterEquiv (G : Type) [Group G] :
    (⊤ : Subgroup G) ⧸ (Subgroup.center G).subgroupOf ⊤ ≃* G ⧸ Subgroup.center G :=
  QuotientGroup.congr _ _ Subgroup.topEquiv (by
    ext x
    simp [Subgroup.mem_map, Subgroup.mem_subgroupOf])

theorem sectionFourHyp_quotient_center (h41 : Item4_1) {G : Type} [Group G] [Finite G]
    (hG : SectionFourHyp G) (hq : IsQuasisimple G) : SectionFourHyp (G ⧸ Subgroup.center G) := by
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2.1
  have hS : IsQuasisimple (G ⧸ Subgroup.center G) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hq.2.2).1
  exact sectionFourHyp_of_mulEquiv (quotientCenterEquiv G)
    (sectionFourHyp_of_section h41 hG ⊤ _
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (quotientCenterEquiv G).symm hS))

end CFSG.RankThree.PartTwo.Sec4.Census
