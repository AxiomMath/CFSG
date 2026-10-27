module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMember
public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourExact
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseE8TwoFrame
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoAFiveE
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwE6TwoFull
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRank
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseE7TwoFrame
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp
import CFSG.LocalAnalysis.StandardType.GGUnitaryTwoBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Field

variable {G : Type} [Group G]

theorem GGRk1ConclEx.n_eq_one_of_card_six {p : ℕ} {Bs X : Subgroup G} {r : MulAut ↥Bs}
    (h : GGRk1ConclEx p Bs X r) (h6 : Nat.card (ggRankOneIn X Bs r) = 6) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hlab : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X)) :
    lab.n = 1 := by
  obtain ⟨F, hF, hFfin, θ, -, hθinj, hθrange, -, -, -, hlabF, -⟩ := h
  have hcardSL : Nat.card (ggRankOneIn X Bs r) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← hθrange]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
  rw [hcardSL, ggSL2_card F] at h6
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hF2 : Nat.card F = 2 := by
    by_contra hne
    have h3 : 3 ≤ Nat.card F := by omega
    have h9 : 9 ≤ Nat.card F ^ 2 := by simpa using Nat.pow_le_pow_left h3 2
    have h24 : 3 * 8 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  have hn : 2 ^ lab.n ≤ 2 := hF2 ▸ hlabF lab hΛ hlab
  have h1 : 1 ≤ lab.n := hΛ.1
  by_contra hne
  have h4 : 2 ^ 2 ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem GGInnerDiagOnLabel.and_n_one_of_card_six {S : ℕ → LargeEvenLabel → Prop} {p : ℕ}
    {Bs X : Subgroup G} (hmark : GGInnerDiagOnLabel S p Bs X) {r : MulAut ↥Bs}
    (h : GGRk1ConclEx p Bs X r) (h6 : Nat.card (ggRankOneIn X Bs r) = 6) :
    GGInnerDiagOnLabel (fun p lab => S p lab ∧ lab.n = 1) p Bs X :=
  hmark.mono_label_of_hasLabel fun _ hΛ hhas hS => ⟨hS, h.n_eq_one_of_card_six h6 hΛ hhas⟩

end Field

section Rows

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

theorem ggX_eRow_of_nonSplit (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hX : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X) (hns : ¬ GGSplitLie p X) :
    GGInnerDiagOnLabel ggRowP_E p Bs X := by
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_E)
      (ggX_ennola_of_nonSplit hcfg hpres hle3 hX hns) with hE | hF4
  · exact hE
  exfalso
  have hle : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hX with hXL | hw
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl hXL)
    · exact hw.2
  obtain ⟨-, hp3⟩ : ∃ _ : True, p = 3 := by
    obtain ⟨lab, -, -, R, _, I, -, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hF4
    exact ⟨trivial, hS.2.1⟩
  subst hp3
  have hmk : GGF4ThreeMarking Bs X := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ?_) hF4
    obtain ⟨⟨htag, -⟩, -, hdvd⟩ := hP.1
    exact ⟨⟨htag, rfl, hdvd⟩, hP.2.1, hP.2.2⟩
  exact ggRow_absurd_F4Three_of_KG1 (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds)
    hcfg hpres hle3 hle hmk

theorem GGSecFiveRouteCfg.eRowTwo_L_of_card_six (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hns : ¬ GGSplitLie p L) {r : MulAut ↥Bs} (hr : GGRk1ConclEx p Bs L r)
    (h6 : Nat.card (ggRankOneIn L Bs r) = 6) :
    GGInnerDiagOnLabel (fun p lab => ggRowP_E p lab ∧ lab.n = 1) p Bs L :=
  (ggX_eRow_of_nonSplit hcfg hpres hle3 (Or.inl rfl) hns).and_n_one_of_card_six hr h6

theorem GGSecFiveRouteCfg.lt_bstar_of_eRowTwo
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_E p lab ∧ lab.n = 1) p Bs L)
    (hU3 : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1) p Bs L → B < Bs)
    (hTwE6 : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs L → B < Bs) :
    B < Bs := by
  have h' : GGInnerDiagOnLabel (fun p lab => (ggRowP_ESU p lab ∧ lab.n = 1) ∨
      ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) ∨ (ggRowP_ETwE6 p lab ∧ lab.n = 1) ∨
      (ggRowP_EE7 p lab ∧ lab.n = 1) ∨ (ggRowP_EE8 p lab ∧ lab.n = 1)) p Bs L :=
    h.mono_label fun lab hl => by
      obtain ⟨hrow, hn⟩ := hl
      rcases hrow with h1 | h1 | h1 | h1 | h1 | h1
      · exact Or.inl ⟨h1, hn⟩
      · exact Or.inr (Or.inl ⟨Or.inl h1, hn⟩)
      · exact Or.inr (Or.inl ⟨Or.inr h1, hn⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h1, hn⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, hn⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, hn⟩)))
  rcases GGInnerDiagOnLabel.elim_or h' with hu | h'
  · have hu' : GGInnerDiagOnLabel (fun p lab => (ggRowP_ESU p lab ∧ lab.n = 1 ∧ ¬ 3 ∣ lab.rank + 1) ∨
        (ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1)) p Bs L :=
      hu.mono_label fun lab hl => by
        by_cases h3 : 3 ∣ lab.rank + 1
        · exact Or.inr ⟨hl.1, hl.2, h3⟩
        · exact Or.inl ⟨hl.1, hl.2, h3⟩
    rcases GGInnerDiagOnLabel.elim_or hu' with hu | hu
    · exact hcfg.1.1.lt_bstar_of_unitaryTwo hu
    · exact hU3 hu
  rcases GGInnerDiagOnLabel.elim_or h' with ho | h'
  · exact GGConfig.lt_bstar_of_orthTwo ggLabelRigidInput_holds hcfg.1.1 ho
  rcases GGInnerDiagOnLabel.elim_or h' with ht | h'
  · exact hTwE6 ht
  rcases GGInnerDiagOnLabel.elim_or h' with h7 | h8
  · exact GGConfig.lt_bstar_of_E7two hcfg.1.1 h7
  · exact hcfg.1.1.lt_bstar_of_E8two h8

theorem GGSecFiveRouteCfg.lt_bstar_or_unitThree_of_eRowTwo (hT : GGSecFiveE6QTwoTimmesfeldInput)
    (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput) (hWI : GGNbrInnerWeylInput)
    (hb1 : FrameRoute.GGFrameTBNumerologyInput) (hb1' : FrameRoute.GGFrameTBVacuousInput)
    (hPU : GGPumpupInput) (hO : FrameRoute.GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hns : ¬ GGSplitLie p L)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_E p lab ∧ lab.n = 1) p Bs L)
    (hU3 : GGIsWeylMatrixE M → GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧ lab.rank ≠ 5) p Bs L → B < Bs)
    (hTwE6 : ¬ GGIsWeylMatrixE M →
      GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs L → B < Bs) :
    B < Bs ∨ (¬ GGIsWeylMatrixE M ∧
      GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1) p Bs L) := by
  classical
  by_cases hu3 : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1) p Bs L
  · by_cases hE : GGIsWeylMatrixE M
    · left
      have hu' : GGInnerDiagOnLabel (fun p lab => (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) ∨
          (ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧ lab.rank ≠ 5)) p Bs L :=
        hu3.mono_label fun lab hl => by
          by_cases h5 : lab.rank = 5
          · exact Or.inl ⟨hl.1, hl.2.1, h5⟩
          · exact Or.inr ⟨hl.1, hl.2.1, hl.2.2, h5⟩
      rcases GGInnerDiagOnLabel.elim_or hu' with h5 | h5
      · exact hcfg.lt_bstar_of_twA5_typeE hT hTB hU62 hpres hE hns h5
      · exact hU3 hE h5
    · exact Or.inr ⟨hE, hu3⟩
  · refine Or.inl (hcfg.lt_bstar_of_eRowTwo h (fun hu => absurd hu hu3) fun ht => ?_)
    by_cases hE : GGIsWeylMatrixE M
    · exact hcfg.lt_bstar_of_twE6Two_typeE hTB hWI hb1 hb1' ggLabelRigidInput_holds hPU hO hTCJ hpres
        hE ht
    · exact hTwE6 hE ht

theorem GGSecFiveRouteCfg.lt_bstar_or_unitThree_of_card_six (hT : GGSecFiveE6QTwoTimmesfeldInput)
    (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput) (hWI : GGNbrInnerWeylInput)
    (hb1 : FrameRoute.GGFrameTBNumerologyInput) (hb1' : FrameRoute.GGFrameTBVacuousInput)
    (hPU : GGPumpupInput) (hO : FrameRoute.GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hns : ¬ GGSplitLie p L) {r : MulAut ↥Bs} (hr : GGRk1ConclEx p Bs L r)
    (h6 : Nat.card (ggRankOneIn L Bs r) = 6)
    (hU3 : GGIsWeylMatrixE M → GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧ lab.rank ≠ 5) p Bs L → B < Bs)
    (hTwE6 : ¬ GGIsWeylMatrixE M →
      GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs L → B < Bs) :
    B < Bs ∨ (¬ GGIsWeylMatrixE M ∧
      GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1) p Bs L) :=
  hcfg.lt_bstar_or_unitThree_of_eRowTwo hT hTB hU62 hWI hb1 hb1' hPU hO hTCJ hpres hns
    (hcfg.eRowTwo_L_of_card_six hpres hle3 hns hr h6) hU3 hTwE6

theorem GGSecFiveRouteCfg.lt_bstar_of_card_six (hT : GGSecFiveE6QTwoTimmesfeldInput)
    (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput) (hWI : GGNbrInnerWeylInput)
    (hb1 : FrameRoute.GGFrameTBNumerologyInput) (hb1' : FrameRoute.GGFrameTBVacuousInput)
    (hPU : GGPumpupInput) (hO : FrameRoute.GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hns : ¬ GGSplitLie p L) {r : MulAut ↥Bs}
    (hr : GGRk1ConclEx p Bs L r) (h6 : Nat.card (ggRankOneIn L Bs r) = 6)
    (hU3 : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧ lab.rank ≠ 5) p Bs L → B < Bs) :
    B < Bs :=
  (hcfg.lt_bstar_or_unitThree_of_card_six hT hTB hU62 hWI hb1 hb1' hPU hO hTCJ hpres hle3 hns hr h6 (fun _ => hU3)
    fun h' => absurd hE h').resolve_right fun h => h.1 hE

end Rows

end CFSG.StandardType

end
