module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGCorFiveTwentyInputNbrQTwoQFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      ¬ GGNbrLabelsOk p B Bs x D J →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem GGCorFiveTwentyInputNbrQTwo.qFour (h : GGCorFiveTwentyInputNbrQTwo) :
    GGCorFiveTwentyInputNbrQTwoQFour :=
  fun G _ _ p B Bs x L D J hH _ hN => h G p B Bs x L D J hH hN

theorem ggCorFiveTwentyInput_of_splitQFour (hQ2 : GGCorFiveTwentyInputQTwo)
    (hRn : GGCorFiveTwentyInputNbrQTwoQFour) (hW : GGCorFiveTwentyQFourInput) :
    GGCorFiveTwentyInput := by
  intro G _ _ p B Bs x L D J hc hop hid hnt hG0
  have hH : GGCorFiveTwentyHyp p B Bs x L D J := ⟨hc, hop, hid, hnt, hG0⟩
  rcases (hid.1.label GGLabQFour p).elim_or with hq | hq
  · by_cases hN : GGNbrLabelsOk p B Bs x D J
    · exact hW G p B Bs x L D J hH hq hN
    · exact hRn G p B Bs x L D J hH hq hN
  · exact hQ2 G p B Bs x L D J hH
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨not_le.mp hP.1, hP.2⟩) hq)

theorem ggCorFiveTwentyInput_of_rootGenQFour (hQ2 : GGCorFiveTwentyInputQTwo)
    (hRn : GGCorFiveTwentyInputNbrQTwoQFour) (hN : GGCorFiveTwentyQFourNonWeylInput)
    (hH : GGHypG0Input) (hL : GGRootGenLInput) (hK : GGRootGenNbrInput) :
    GGCorFiveTwentyInput :=
  ggCorFiveTwentyInput_of_splitQFour hQ2 hRn
    (ggCorFiveTwentyQFourInput_of_weyl hN (ggCorFiveTwentyQFourWeylInput_of_rootGen hH hL hK))

end CFSG.StandardType
