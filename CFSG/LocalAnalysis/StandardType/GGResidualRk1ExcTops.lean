module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGNSJoinByType
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import Certificates.Certificate1952
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6PatCox
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6PatRows
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaForkCox
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlus
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTwE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTwE6Three
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaOrth
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggResidual_excRow_absurd_AD
    (hRig : GGLabelRigidInput) (hRk : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hAD : GGIsWeylMatrixA M ∨ NSJoin.NSTypeD M)
    {X : Subgroup G} (hXw : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∨ ggRowP_EE7 p lab ∨
      ggRowP_EE8 p lab) p Bs X) :
    False := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hX : X = L ∨ ∃ y, GGNbr p B x D J y X := by
    rcases hXw with rfl | hw
    · exact Or.inl rfl
    · exact Or.inr hw.1
  have hle : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hXw with rfl | hw
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
    · exact hw.2
  have hrow : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∨ (ggRowP_EE7 p lab ∨
      ggRowP_EE8 p lab)) p Bs X := h
  have hDcase : NSJoin.NSTypeD M → False := by
    intro hD
    have hNP : GGNoReflE6Pat p Bs X := ggX_noReflE6Pat_typeD hcfg hpres hD hle
    rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_ETwE6) hrow with hTw | hRest
    · by_cases hp3 : p = 3
      · subst hp3
        have hrow3 : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ p = 3) 3 Bs X :=
          hTw.mono_label (fun lab hl => ⟨hl, rfl⟩)
        have hLab : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs X := by
          refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hrow3
          obtain ⟨⟨htag, hdvd⟩, hp3⟩ := hP.1
          refine ⟨⟨htag, hp3, hp3 ▸ hdvd⟩, Or.inr (Or.inl ⟨?_, ?_, hdvd⟩), hP.2.1, hP.2.2⟩
          · rw [htag]; exact fun h => h
          · rw [htag]; simp
        have hLab' : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs X := hLab
        have hrk : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
            3 ^ 5 ≤ Nat.card (ggGamma X hN).range := by
          intro hN
          rcases hX with hXL | ⟨y, hnb⟩
          · subst X
            exact ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hcfg.1.1 hLab hN
          · exact hRk G 3 B Bs x L D J hcfg.1.1 rfl y X hnb hLab' hN
              (ggTorusSelfCent_ggGamma hN hcfg.1.1.2.1.2.2.2)
        exact ggX_row_absurd_of_noReflE6PatAt hRig (by norm_num)
          ggRowE6PatAt_ETwE6_three hcfg hX hNP hrk hrow3
      · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
        have hrow5 : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 5 ≤ p) p Bs X :=
          hTw.mono_label (fun lab hl => ⟨hl, hp5⟩)
        exact ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_ETwE6_ge5 hcfg hX hNP hrow5
    · rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EE7) hRest with hE7 | hE8
      · exact ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_EE7 hcfg hX hNP hE7
      · exact ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_EE8 hcfg hX hNP hE8
  have hAcase : GGIsWeylMatrixA M → False := by
    intro hA
    obtain ⟨m, σ, -, hM⟩ := hA
    have hNF : GGNoReflFork p Bs X := ggX_noReflFork_typeA hcfg hpres hM h3 hle
    rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_ETwE6) hrow with hTw | hRest
    · by_cases hp3 : p = 3
      · subst hp3
        have hrow3 : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ p = 3) 3 Bs X :=
          hTw.mono_label (fun lab hl => ⟨hl, rfl⟩)
        have hLab : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs X := by
          refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hrow3
          obtain ⟨⟨htag, hdvd⟩, hp3⟩ := hP.1
          refine ⟨⟨htag, hp3, hp3 ▸ hdvd⟩, Or.inr (Or.inl ⟨?_, ?_, hdvd⟩), hP.2.1, hP.2.2⟩
          · rw [htag]; exact fun h => h
          · rw [htag]; simp
        have hLab' : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs X := hLab
        have hrk : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
            3 ^ 5 ≤ Nat.card (ggGamma X hN).range := by
          intro hN
          rcases hX with hXL | ⟨y, hnb⟩
          · subst X
            exact ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hcfg.1.1 hLab hN
          · exact hRk G 3 B Bs x L D J hcfg.1.1 rfl y X hnb hLab' hN
              (ggTorusSelfCent_ggGamma hN hcfg.1.1.2.1.2.2.2)
        exact ggX_row_absurd_of_noReflForkAt hRig (by norm_num)
          ggRowForkAt_ETwE6_three hcfg hX hNF hrk hrow3
      · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
        have hrow5 : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 5 ≤ p) p Bs X :=
          hTw.mono_label (fun lab hl => ⟨hl, hp5⟩)
        exact ggX_row_absurd_of_noReflFork hRig ggRowFork_ETwE6_ge5 hcfg hX hNF hrow5
    · rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EE7) hRest with hE7 | hE8
      · exact ggX_row_absurd_of_noReflFork hRig ggRowFork_EE7 hcfg hX hNF hE7
      · exact ggX_row_absurd_of_noReflFork hRig ggRowFork_EE8 hcfg hX hNF hE8
  rcases hAD with hA | hD
  · exact hAcase hA
  · exact hDcase hD

theorem ggResidual_orthRow_absurd_A
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hA : GGIsWeylMatrixA M)
    {X : Subgroup G} (hXw : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) p Bs X) :
    False := by
  obtain ⟨m, σ, -, hM⟩ := hA
  have hX : X = L ∨ ∃ y, GGNbr p B x D J y X := by
    rcases hXw with rfl | hw
    · exact Or.inl rfl
    · exact Or.inr hw.1
  have hle : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hXw with rfl | hw
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
    · exact hw.2
  have hNF : GGNoReflFork p Bs X := ggX_noReflFork_typeA hcfg hpres hM h3 hle
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EOmP) h with hP | hOm
  · exact ggX_row_absurd_of_noReflFork hRig ggRowFork_EOmP hcfg hX hNF hP
  · exact ggX_row_absurd_of_noReflFork hRig ggRowFork_EOmM hcfg hX hNF hOm

end CFSG.StandardType

end
