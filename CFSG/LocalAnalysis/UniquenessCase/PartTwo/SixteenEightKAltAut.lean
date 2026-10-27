module

import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbedding.AltBetaRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16k_pRank_aut_alt {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 5 ≤ n)
    (hX : UC22.IsAlt X n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ n / p := by
  obtain ⟨e⟩ := hX
  by_cases hn6 : n = 6
  · subst hn6
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr e)]
    exact CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_mulAut_alternating_six_le hp hp2
  · exact CFSG.AGLEmbedding.pRank_top_mulAut_le hn hn6 e hp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
