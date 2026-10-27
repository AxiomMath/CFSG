module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyA11
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGCorFiveTwentyR3Rank {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (D J : Subgroup G) : Prop :=
  ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
    GGInnerDiagOnLab (fun p lab => GGTwE6BadLabel p lab ∧ GGLabQTwo p lab) p Bs K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G), 3 ^ 5 ≤ Nat.card (ggGamma K hN).range

@[expose] def GGCorFiveTwentyInputNbrQTwoQFourNoA11CfgR3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      ¬ GGNbrLabelsOk p B Bs x D J → ¬ GGSecFiveA11Config p B Bs x L D J →
        GGCorFiveTwentyR3Rank p B Bs x D J →
          Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem GGCorFiveTwentyInputNbrQTwoQFourNoA11Cfg.toR3Rank
    (h : GGCorFiveTwentyInputNbrQTwoQFourNoA11Cfg) : GGCorFiveTwentyInputNbrQTwoQFourNoA11CfgR3 :=
  fun G _ _ p B Bs x L D J hH hq hN hA _ => h G p B Bs x L D J hH hq hN hA

theorem ggCorFiveTwentyR3Rank_of_rank (hR : GGTwE6ThreeNbrRankInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGCorFiveTwentyHyp p B Bs x L D J) : GGCorFiveTwentyR3Rank p B Bs x D J := by
  intro y K hK hInn hN
  obtain ⟨lab, -, -, -, -, -, -, -, ⟨⟨hbl, -⟩, -⟩⟩ := largeEvenMarking_exists_hasLabel hInn
  have hp3 : p = 3 := hbl.2.1
  subst hp3
  exact hR G 3 B Bs x L D J hH.1 rfl y K hK
    (hInn.mono fun _ _ h => h.1) hN (ggTorusSelfCent_ggGamma hN hH.1.2.1.2.2.2)

theorem GGCorFiveTwentyInputNbrQTwoQFourNoA11Cfg.of_r3Rank (hR : GGTwE6ThreeNbrRankInput)
    (h : GGCorFiveTwentyInputNbrQTwoQFourNoA11CfgR3) :
    GGCorFiveTwentyInputNbrQTwoQFourNoA11Cfg :=
  fun G _ _ p B Bs x L D J hH hq hN hA =>
    h G p B Bs x L D J hH hq hN hA (ggCorFiveTwentyR3Rank_of_rank hR hH)

end CFSG.StandardType
