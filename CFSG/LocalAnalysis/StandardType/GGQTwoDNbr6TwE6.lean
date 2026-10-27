module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoPThree

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan

section


theorem qtwoDNbr_twE6_rank (h : GGTwE6ThreeNbrRankInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hconf : GGConfig 3 B Bs x L D J) {y : G}
    {X : Subgroup G} (hnbr : GGNbr 3 B x D J y X)
    (hmk : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ p = 3) 3 Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) : 3 ^ 5 ≤ Nat.card (ggGamma X hN).range := by
  have hmk' : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs X :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ hP => by
      obtain ⟨⟨⟨htag, hd⟩, -⟩, hN', hind⟩ := hP
      refine ⟨⟨htag, rfl, hd⟩, Or.inr (Or.inl ⟨?_, ?_, hd⟩), hN', hind⟩
      · rw [htag]
        exact fun h => h
      · rw [htag]
        decide) hmk
  exact h G 3 B Bs x L D J hconf rfl y X hnbr hmk' hN
    (ggTorusSelfCent_ggGamma hN hconf.2.1.2.2.2)

theorem ggQTwoDSixTwE6InputOn_of_nbrRank {R : ℕ → Prop} (h : GGTwE6ThreeNbrRankInput) :
    GGQTwoDSixTwE6InputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hRm hm6 hM y X hnbr hmk hN
  obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
  have hp3 : p = 3 := ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp3
  exact qtwoDNbr_twE6_rank h hcfg.1.1.1 hnbr hmk hN

end

end CFSG.StandardType.QTwo

end
