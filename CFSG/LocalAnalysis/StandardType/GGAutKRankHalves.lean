module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKRankDefs
public import CFSG.LocalAnalysis.StandardType.GGAutKSummandStruct

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Halves

theorem ggAutKCanonIIIFlatInputRk_iff :
    GGAutKCanonIIIFlatInputRk ↔ GGAutKCanonIIIFlatInputRkTwo ∧ GGAutKCanonIIIFlatInputTable := by
  constructor
  · intro h
    exact ⟨fun G _ _ p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg hrk hN =>
        h G p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg (Or.inl hrk),
      fun G _ _ p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg hrk hN =>
        h G p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg (Or.inr hrk)⟩
  · rintro ⟨h1, h2⟩ G _ _ p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg hrk hN
    rcases hrk with hrk | hrk
    · exact h1 G p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg hrk
    · exact h2 G p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg hrk

theorem ggAutKCanonIIIFlatInputRkTwo_of_known (hO : GGOTwoCentralizerInputRankTwo)
    (hE : GGE0InnerDiagInput) (h1c : GGStructSOneComp) (h1d : GGStructSOnePerf) :
    GGAutKCanonIIIFlatInputRkTwo := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg hrk hN
  obtain ⟨hb, hb1, hL₁, hK, hLK, hKM, hm, hEC⟩ := hcfg
  have hcfg : GGAutKConjConfig p B Bs x L D J b L₁ K m := ⟨hb, hb1, hL₁, hK, hLK, hKM, hm, hEC⟩
  exact ggHypRestIIIFlat_of_summandStruct hctx s1 hcfg
    (ggSummandStruct_of_O2 hE h1c h1d hctx s1 hcfg
      (hO G p B Bs x L D J t n f ψ hctx s1 b L₁ hb hb1 hL₁ hrk m hm hEC))

end Halves

end CFSG.StandardType
