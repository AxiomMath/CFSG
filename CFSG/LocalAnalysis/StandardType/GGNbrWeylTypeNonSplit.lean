module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeGlue
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section K

theorem ggNbrWeylTypeNonSplitInput_of_weylType
    (hW : GGNbrTableBWeylTypeNonSplitOn fun p lab =>
      ¬ GGF4ThreeLabel p lab ∧ ¬ GGUSixThreeLabel p lab)
    (hF4R : GGF4ThreeNbrRankInput) (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hF4W : GGF4ThreeNbrWeylTypeInput) (hU6W : GGUSixThreeNbrWeylTypeInput) :
    GGNbrWeylTypeNonSplitInput := by
  intro G _ _ p B Bs x L D J h y K hK hns hq
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hcfg : GGConfig p B Bs x L D J := h.1
  have hNoTr : GGNoTransvection p Bs := h.2.2.2.1
  have hInnK : GGInnerDiagOn Bs K := h.2.2.1.2 y K hK
  have hZK := ggNbrBstarCenterInput_of_centerPCyclic ggLabelCenterPCyclicInput_holds
    G p B Bs x L D J h y K hK
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  obtain ⟨lab, hlab, hhas, hns'⟩ := exists_nonSplitLabel_of_nbr h hK hns hq
  by_cases hF4 : GGF4ThreeLabel p lab
  ·
    obtain rfl : p = 3 := hF4.2.1
    have hInnL : LargeEvenMarking ↥K (fun lab' _ _ I _ θ => GGF4ThreeLabel 3 lab' ∧
        Bs ≤ Subgroup.normalizer (K : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
      largeEvenMarking_mono (fun _ _ _ _ _ _ hP => by
          obtain ⟨rfl, hN', hind⟩ := hP
          exact ⟨hF4, hN', hind⟩)
        (ggInnerDiagOn_relabel hRig hInnK hlab hhas)
    obtain ⟨R, _, θ, I, F, hBsI, hWR⟩ :=
      exists_innerDiagDatum_of_labelAll hRig hInnK hlab hhas
        (hF4W lab hlab hF4) hN
    exact ggWeylReflectionGroup_of_ggTorusWeylTypeW_card hcfg (by norm_num) hNoTr hK hInnK.1 θ hN hBsI
      (hF4R G 3 B Bs x L D J hcfg hNoTr rfl y K hK hInnL hN
        (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2)) hWR hZK
  by_cases hU6 : GGUSixThreeLabel p lab
  ·
    obtain rfl : p = 3 := hU6.2.2.1
    have hInnL := ggInnerDiagOnLab_of_hasLabel hRig hInnK hlab hhas hU6
      (Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, hU6.1], by simp [hU6.1], hU6.2.2.2⟩))
    obtain ⟨R, _, θ, I, F, hBsI, hWR⟩ :=
      exists_innerDiagDatum_of_labelAll hRig hInnK hlab hhas (hU6W lab hlab hU6) hN
    exact ggWeylReflectionGroup_of_ggTorusWeylTypeW_card hcfg (by norm_num) hNoTr hK hInnK.1 θ hN hBsI
      (ggUSixThreeNbrRankInput_of_balance hL hPJ G 3 B Bs x L D J hcfg hNoTr rfl y K hK hInnL hN
        (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2)) hWR hZK
  obtain ⟨R, _, θ, I, F, hBsI, r, hlift, hT⟩ := exists_innerDiagDatum_of_labelAll_simple hRig hInnK
    hlab hhas (hW p hcfg.1.2.2.2.2.2.1.1 hcfg.1.2.2.2.2.2.1.2.1 lab hlab ⟨hF4, hU6⟩ hns') hN
  exact ggWeylReflectionGroup_of_ggTorusWeylTypeW hcfg hNoTr hK hInnK.1 θ hN hBsI hlift hT hZK

end K

section Families

theorem ggNbrTableBWeylTypeNonSplitOn_of_families
    (hV : GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitVacLabel)
    (hC1 : GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitUnitaryLabel)
    (hC2 : GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitUnitaryHypLabel)
    (hC3 : GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitOrthLabel)
    (hC4 : GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitSympLinLabel)
    (hE3 : GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitExcPlusLabel)
    (hE4 : GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitE6TwoLabel)
    (hE5 : GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitTwE6Label) :
    GGNbrTableBWeylTypeNonSplitOn fun p lab => ¬ GGF4ThreeLabel p lab ∧ ¬ GGUSixThreeLabel p lab := by
  intro p hp hp2 lab hlab hU hns
  rcases ggNbrNonSplitLabel_cover hp hp2 hlab hns hU.1 hU.2 with h | h | h | h | h | h | h | h
  · exact hV p hp hp2 lab hlab h hns
  · exact hC1 p hp hp2 lab hlab h hns
  · exact hC2 p hp hp2 lab hlab h hns
  · exact hC3 p hp hp2 lab hlab h hns
  · exact hC4 p hp hp2 lab hlab h hns
  · exact hE3 p hp hp2 lab hlab h hns
  · exact hE4 p hp hp2 lab hlab h hns
  · exact hE5 p hp hp2 lab hlab h hns

end Families

section TwE6

variable {G : Type} [Group G] [Finite G]

theorem ggNbrWeylReflGroup_of_twE6Three (hR : GGTwE6ThreeNbrRankInput)
    (hW : GGTwE6ThreeNbrWeylTypeInput) (hRig : GGLabelRigidInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K)
    (hbad : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGTwE6BadLabel p lab)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) :
    GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
      ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs) := by
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, hbl⟩ := largeEvenMarking_exists_hasLabel hbad
  have hp3 : p = 3 := hbl.2.1
  subst hp3
  have hInnL := ggInnerDiagOnLab_of_twE6BadMarking hRig hInnK hbad
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  have h5 := hR G 3 B Bs x L D J hcfg rfl y K hnb hInnL hN
    (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2)
  obtain ⟨R, _, θ, I, F, hBsI, hWR⟩ :=
    exists_innerDiagDatum_of_labelAll hRig hInnK hlab hhas (hW lab hlab hbl) hN
  exact ggWeylReflectionGroup_of_ggTorusWeylTypeW_card hcfg (by norm_num) hNoTr hnb hInnK.1 θ hN
    hBsI h5 hWR hZ

theorem ggNbrWeylTypeNonSplitFull_of_rank (h : GGNbrWeylTypeNonSplitInput)
    (hR : GGTwE6ThreeNbrRankInput) (hW : GGTwE6ThreeNbrWeylTypeInput) (hRig : GGLabelRigidInput)
    (hZ : GGNbrBstarCenterInput) : GGNbrWeylTypeNonSplitFull := by
  intro G _ _ p B Bs x L D J hRest y K hK hns hq
  have hDisj : LargeEvenMarking ↥K (fun lab _ _ _ _ _ =>
      (p ∣ (2 ^ lab.n) ^ 2 - 1 ∧ ¬ GGTwE6BadLabel p lab) ∨ GGTwE6BadLabel p lab) :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ hd => by
      by_cases hb : GGTwE6BadLabel p lab
      · exact Or.inr hb
      · exact Or.inl ⟨hd, hb⟩) hq
  rcases largeEvenMarking_or hDisj with hq' | hbad
  · exact h G p B Bs x L D J hRest y K hK hns hq'
  · exact ggNbrWeylReflGroup_of_twE6Three hR hW hRig hRest.1 hRest.2.2.2.1 hK
      (hRest.2.2.1.2 y K hK) hbad (hZ G p B Bs x L D J hRest y K hK)

end TwE6


section Pump

theorem ggSecFivePumpNbrNSInput_of_parts
    (hS : GGSecFivePumpNbrNSSplitInput) (hC4 : GGNbrExcSevenReflInput)
    (hFull : GGNbrWeylTypeNonSplitFull) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) : GGSecFivePumpNbrNSInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL y K hK hnsK
  have h : GGSecFiveRestHyp p B Bs x L D J := hcfg.1
  have hHS := ggNbr_halfSplit_of_secFiveRest hraw hiso h hK
  by_cases hsp : LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GGNbrSplitLabel p lab)
  · exact hS G p B Bs x L D J 𝒦 hcfg hL y K hK hnsK hsp
  by_cases hq : LargeEvenMarking ↥K (fun lab _ _ _ _ _ => p ∣ (2 ^ lab.n) ^ 2 - 1)
  · exact hFull G p B Bs x L D J h y K hK hsp hq
  exfalso
  have hDisj : LargeEvenMarking ↥K (fun lab _ _ _ _ _ =>
      p ∣ (2 ^ lab.n) ^ 2 - 1 ∨ (p = 7 ∧ (lab = ⟨.A, 8, 1⟩ ∨ lab = ⟨.E6, 0, 1⟩))) :=
    ggMarking_mono_lab (fun lab _ _ _ _ _ hlab hP => largeEvenHalfSplit_dvd hlab hP) hHS
  rcases largeEvenMarking_or hDisj with hd | hex
  · exact hq hd
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, hp7, hl⟩ := largeEvenMarking_exists_hasLabel hex
  have hrefl : GGReflGenerated p (ggAutomizer K Bs) := hcfg.2.1 y K hK
  refine hC4 G p B Bs x L D J h y K hK hp7 ?_ hrefl
  rcases hl with rfl | rfl
  · exact Or.inl hhas
  · exact Or.inr hhas

end Pump

end CFSG.StandardType

end
