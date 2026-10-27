module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeO2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NePair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NePairConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeTri
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ACClos
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23ne_false_of_ns (D : Data G) (h126 : R126 D) (h63 : R16_63 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_2 D V₀ V hV L) (h154 : Hyp154 D V₀ V L)
    (hne : v1Sub D.M V₀ V hV L ≠ ⊥) {x : G} {K₁ K₂ : Subgroup G}
    (hns : C23NeNs D V₀ V L hV x K₁ K₂) : False := by
  have hP := c23ne_pair_of_ns D h154 hns
  have hN : normalizer (V : Set G) = D.M :=
    normalizer_eq_of_inCalV D (hyp123_inCalV h154.hyp151.hyp125.1)
  have hk := TwelveSeven.k_le_two D
  rcases trichotomy_of_lt D h126 h154.hyp151.hyp125 (c23ne_lt_rParam hk hP hN)
      (c23ne_lt_betaN hk hP (c23ne_twoElt_of_ns hns)) with h1 | h2 | ⟨_, g, rfl, hg⟩
  · exact h1 (h63 V₀ V L hV hS ⟨Or.inl hc, h154⟩).2
  · exact h2 (c23a_centralizer_cClos_le D h154 hne D.k)
  · exact c23ne_false_of_inCalO2 hk hP (c23ne_pair_conj g hP) hg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
