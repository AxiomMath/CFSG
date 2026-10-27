module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaForkCox
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaOrth
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlus
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTwE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSExcl
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola
public import Certificates.Certificate43
public import Certificates.Certificate1952
public import Certificates.Certificate3951
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeHolds
import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRank
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveNSEnnola_core_of_noReflFork
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G}
    (hX : X = L ∨ ((∃ y, GGNbr p B x D J y X) ∧ ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦))
    (hNF : GGNoReflFork p Bs X)
    (hrk3 : p = 3 → GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs X →
      ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), p ^ 5 ≤ Nat.card (ggGamma X hN).range)
    (hrow : GGInnerDiagOnLabel (fun p lab => ggRowP_Ennola p lab ∧ ¬ ggRowP_ESU p lab) p Bs X) :
    False := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hX' : X = L ∨ ∃ y, GGNbr p B x D J y X := hX.imp_right And.left
  have hle : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hX with rfl | ⟨-, hle⟩
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
    · exact hle
  have h5 : p = 3 ∨ 5 ≤ p := by
    by_cases h3 : p = 3
    · exact Or.inl h3
    · exact Or.inr (hp.five_le_of_ne_two_of_ne_three hodd h3)
  have h6 : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab ∨
      (ggRowP_ETwE6 p lab ∧ 5 ≤ p) ∨ (ggRowP_ETwE6 p lab ∧ p = 3) ∨ ggRowP_EE7 p lab ∨
      ggRowP_EE8 p lab ∨ (ggRowP_NF4 p lab ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1)) p Bs X := by
    refine hrow.mono' fun lab h => ?_
    obtain ⟨hE, hnESU⟩ := h
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
  · exact ggX_row_absurd_of_noReflFork hRig ggRowFork_EOmP hcfg hX' hNF h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EOmM) h with h | h
  · exact ggX_row_absurd_of_noReflFork hRig ggRowFork_EOmM hcfg hX' hNF h
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_ETwE6 p lab ∧ 5 ≤ p) h with h | h
  · exact ggX_row_absurd_of_noReflFork hRig ggRowFork_ETwE6_ge5 hcfg hX' hNF h
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => ggRowP_ETwE6 p lab ∧ p = 3) h with h | h
  ·
    have hLab : GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs X := by
      refine largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ?_) h
      obtain ⟨⟨htag, hdvd⟩, hp3⟩ := hP.1
      refine ⟨⟨htag, hp3, hp3 ▸ hdvd⟩, Or.inr (Or.inl ⟨by rw [htag]; exact fun h => h,
        by rw [htag]; simp, hdvd⟩), hP.2.1, hP.2.2⟩
    have hp3 : p = 3 := by
      obtain ⟨lab, -, -, R, _, I, -, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel h
      exact hS.2
    have hrk := hrk3 hp3 hLab
    exact ggX_row_absurd_of_noReflForkAt hRig (by norm_num) ggRowForkAt_ETwE6_three hcfg hX' hNF
      hrk h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EE7) h with h | h
  · exact ggX_row_absurd_of_noReflFork hRig ggRowFork_EE7 hcfg hX' hNF h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EE8) h with h | h
  · exact ggX_row_absurd_of_noReflFork hRig ggRowFork_EE8 hcfg hX' hNF h
  obtain ⟨-, hp3⟩ : ∃ _ : True, p = 3 := by
    obtain ⟨lab, -, -, R, _, I, -, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel h
    exact ⟨trivial, hS.2.1⟩
  subst hp3
  have hF4 : GGF4ThreeMarking Bs X := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ?_) h
    obtain ⟨⟨htag, -⟩, -, hdvd⟩ := hP.1
    exact ⟨⟨htag, rfl, hdvd⟩, hP.2.1, hP.2.2⟩
  exact ggRow_absurd_F4Three_of_KG1 (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds)
    hcfg hpres hle3 hle hF4

end CFSG.StandardType

end
