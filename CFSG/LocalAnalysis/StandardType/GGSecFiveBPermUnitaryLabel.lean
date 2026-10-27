module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaCore
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberNoPair
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeHolds
import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRank
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1DSmall
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggL_esu_of_noPair_noFork
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hNP : GGNoReflFramePair p Bs L) (hNF : GGNoReflFork p Bs L)
    (hrow : GGInnerDiagOnLabel ggRowP_Ennola p Bs L) :
    GGInnerDiagOnLabel ggRowP_ESU p Bs L := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hX' : L = L ∨ ∃ y, GGNbr p B x D J y L := Or.inl rfl
  have h5 : p = 3 ∨ 5 ≤ p := by
    by_cases h3 : p = 3
    · exact Or.inl h3
    · exact Or.inr (hp.five_le_of_ne_two_of_ne_three hodd h3)
  have hsplit : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∨
      (ggRowP_Ennola p lab ∧ ¬ ggRowP_ESU p lab)) p Bs L :=
    hrow.mono' fun lab h => by
      by_cases hESU : ggRowP_ESU p lab
      · exact Or.inl hESU
      · exact Or.inr ⟨h, hESU⟩
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_ESU) hsplit with hE | h
  · exact hE
  have h6 : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab ∨
      (ggRowP_ETwE6 p lab ∧ 5 ≤ p) ∨ (ggRowP_ETwE6 p lab ∧ p = 3) ∨ ggRowP_EE7 p lab ∨
      ggRowP_EE8 p lab ∨ (ggRowP_NF4 p lab ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1)) p Bs L := by
    refine h.mono' fun lab h' => ?_
    obtain ⟨hE, hnESU⟩ := h'
    rcases hE with (hESU | hOmP | hOmM | hTw | hE7 | hE8) | hF4
    · exact absurd hESU hnESU
    · exact Or.inl hOmP
    · exact Or.inr (Or.inl hOmM)
    · rcases h5 with h3 | h5
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hTw, h3⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨hTw, h5⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE7))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE8)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hF4)))))
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EOmP) h6 with h | h
  · exact False.elim (ggX_row_absurd_of_noReflFork hRig ggRowFork_EOmP hcfg hX' hNF h)
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EOmM) h with h | h
  · exact False.elim (ggX_row_absurd_of_noReflFork hRig ggRowFork_EOmM hcfg hX' hNF h)
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_ETwE6 p lab ∧ 5 ≤ p) h with h | h
  · exact False.elim (ggX_row_absurd_of_noReflFork hRig ggRowFork_ETwE6_ge5 hcfg hX' hNF h)
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_ETwE6 p lab ∧ p = 3) h with h | h
  ·
    have hLab : GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs L := by
      refine largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ?_) h
      obtain ⟨⟨htag, hdvd⟩, hp3⟩ := hP.1
      refine ⟨⟨htag, hp3, hp3 ▸ hdvd⟩, Or.inr (Or.inl ⟨by rw [htag]; exact fun h => h,
        by rw [htag]; simp, hdvd⟩), hP.2.1, hP.2.2⟩
    have hp3 : p = 3 := by
      obtain ⟨lab, -, -, R, _, I, -, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel h
      exact hS.2
    subst hp3
    have hrk : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
        3 ^ 5 ≤ Nat.card (ggGamma L hN).range :=
      fun hN => ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hcfg.1.1 hLab hN
    exact False.elim (ggX_row_absurd_of_noReflForkAt hRig (by norm_num) ggRowForkAt_ETwE6_three
      hcfg hX' hNF hrk h)
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EE7) h with h | h
  · exact False.elim (ggX_row_absurd_of_noReflFork hRig ggRowFork_EE7 hcfg hX' hNF h)
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EE8) h with h | h
  · exact False.elim (ggX_row_absurd_of_noReflFork hRig ggRowFork_EE8 hcfg hX' hNF h)
  obtain ⟨-, hp3⟩ : ∃ _ : True, p = 3 := by
    obtain ⟨lab, -, -, R, _, I, -, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel h
    exact ⟨trivial, hS.2.1⟩
  subst hp3
  have hF4 : GGF4ThreeMarking Bs L := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ?_) h
    obtain ⟨⟨htag, -⟩, -, hdvd⟩ := hP.1
    exact ⟨⟨htag, rfl, hdvd⟩, hP.2.1, hP.2.2⟩
  exact False.elim (hNP (ggF4Three_framePair_of_rank hcfg.1.1 hF4 fun hN =>
    ggF4Three_rank_of_marking (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds)
      hcfg.1.1 hcfg.1.2.2.2.1 hF4 hN))

theorem ggSecFiveBPermUnitaryLabelInput_holds :
    GGSecFiveBPermUnitaryLabelInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hne n eta _hJoin hAut
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have hns : ¬ GGSplitLie p L := fun h => hne (ggSecFiveRoute_bstar_eq_of_split hR h).symm
  have hNP : GGNoReflFramePair p Bs L := ggNoReflFramePair_of_aPermutationFull hp hp2 eta hAut
  have hNF : GGNoReflFork p Bs L := ggNoReflFork_of_aPermutationFull hp hp2 eta hAut
  have hESU : GGInnerDiagOnLabel ggRowP_ESU p Bs L :=
    ggL_esu_of_noPair_noFork hR hNP hNF (ggL_ennola_of_nonSplit_of_noPair hR hNP hns)
  obtain ⟨lab, -, hhas, R, _, I, F, θ, hQ⟩ := largeEvenMarking_exists_hasLabel hESU
  obtain ⟨t, r, f⟩ := lab
  obtain ⟨hdisj, hdvd⟩ := hQ.1
  rcases hdisj with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
  · exact ⟨r, f, hr, hdvd, hhas⟩
  · subst hr
    refine ⟨3, f, le_rfl, hdvd, ?_⟩
    have hhasA : GGHasLabel (⟨.twA, 3, f⟩ : LargeEvenLabel)
        (L ⧸ Subgroup.center L) := by
      unfold GGHasLabel at hhas ⊢
      exact largeEvenRawDatum_of_ggLabelIso
        (CFSG.StandardType.Q1DSmall.labelIso_twD3_twA3 f) hhas
    exact hhasA

end CFSG.StandardType

end
