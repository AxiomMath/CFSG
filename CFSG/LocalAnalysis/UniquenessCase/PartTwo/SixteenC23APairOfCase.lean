module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModCase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ABridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23a_pair_of_case (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Case167_2 D V₀ V hV L) (h : Hyp154 D V₀ V L)
    (h0 : V₀ = ⊥) (hne : v1Sub D.M V₀ V hV L ≠ ⊥) :
    ∃ x ∈ D.M, C23APair D.M V (wSub V₀ V hV L) (conjSubgroup (wSub V₀ V hV L) x) := by
  obtain ⟨x, hx, hP⟩ := c23a_modPair_of_case D h1217 hc h.hyp151 h0 hne
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hw : wSub V₀ V hV (conjSubgroup L x) = conjSubgroup (wSub V₀ V hV L) x :=
    s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hx)
  subst h0
  refine ⟨x, hx, ?_⟩
  rw [← hw]
  exact c23a_pair_of_modPair hV h.hyp151.hyp125.pairFacts.le_normalizer hP fun w hw' hw1 =>
    c23a_cent_union D h hx (hw ▸ hw') hw1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
