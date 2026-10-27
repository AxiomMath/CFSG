module

public import CFSG.LocalAnalysis.StandardType.GGAutKRankHalves
public import CFSG.LocalAnalysis.StandardType.GGSixAutKStarDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section HalvesStar

theorem ggOTwoCentralizerInputRankTwo_of_star (h : GGOTwoCentralizerInputStar) :
    GGOTwoCentralizerInputRankTwo :=
  fun G _ _ p B Bs x L D J t n f ψ hctx s1 b L₁ hb hb1 hL₁ _ m hm hEC =>
    h G p B Bs x L D J t n f ψ hctx s1 b L₁ hb hb1 hL₁ m hm hEC

theorem ggAutKCanonIIIFlatInputTable_of_star (hO : GGOTwoCentralizerInputStar)
    (hE : GGE0InnerDiagInput) (h1c : GGStructSOneComp) (h1d : GGStructSOnePerf) :
    GGAutKCanonIIIFlatInputTable := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg _ hN
  obtain ⟨hb, hb1, hL₁, hK, hLK, hKM, hm, hEC⟩ := hcfg
  have hcfg : GGAutKConjConfig p B Bs x L D J b L₁ K m := ⟨hb, hb1, hL₁, hK, hLK, hKM, hm, hEC⟩
  exact ggHypRestIIIFlat_of_summandStruct hctx s1 hcfg
    (ggSummandStruct_of_O2 hE h1c h1d hctx s1 hcfg
      (hO G p B Bs x L D J t n f ψ hctx s1 b L₁ hb hb1 hL₁ m hm hEC))

theorem ggAutKCanonIIIFlatInputRk_of_star (hO : GGOTwoCentralizerInputStar)
    (hE : GGE0InnerDiagInput) (h1c : GGStructSOneComp) (h1d : GGStructSOnePerf) :
    GGAutKCanonIIIFlatInputRk :=
  ggAutKCanonIIIFlatInputRk_iff.mpr
    ⟨ggAutKCanonIIIFlatInputRkTwo_of_known (ggOTwoCentralizerInputRankTwo_of_star hO) hE h1c h1d,
      ggAutKCanonIIIFlatInputTable_of_star hO hE h1c h1d⟩

end HalvesStar

end CFSG.StandardType
