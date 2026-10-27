module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AO2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23APairConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23APairOfCase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ATri
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ACClos
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23a_false_of_v0_bot (D : Data G) (h126 : R126 D) (h1217 : R1217 D) (h63 : R16_63 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_2 D V₀ V hV L) (h : Hyp154 D V₀ V L) (h0 : V₀ = ⊥)
    (hne : v1Sub D.M V₀ V hV L ≠ ⊥) : False := by
  obtain ⟨x, -, hP⟩ := c23a_pair_of_case D h1217 hc h h0 hne
  have hN : normalizer (V : Set G) = D.M :=
    normalizer_eq_of_inCalV D (hyp123_inCalV h.hyp151.hyp125.1)
  have hk := TwelveSeven.k_le_two D
  rcases trichotomy_of_lt D h126 h.hyp151.hyp125 (c23a_lt_rParam hk hP hN)
      (c23a_lt_betaN hk hP) with h1 | h2 | ⟨_, g, rfl, hg⟩
  · exact h1 (h63 V₀ V L hV hS ⟨Or.inl hc, h⟩).2
  · exact h2 (c23a_centralizer_cClos_le D h hne D.k)
  · exact c23a_false_of_inCalO2 hk hP (c23a_pair_conj g hP) hg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
