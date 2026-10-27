module

public import CFSG.LocalAnalysis.StandardType.GGRootGenResQFourDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem l05nTRT_largeEvenSplit_of_twE6BadLabel {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTwE6BadLabel p lab) : LargeEvenSplit p lab := by
  unfold GGTwE6BadLabel at h
  obtain ⟨ht, hp, hdvd⟩ := h
  subst hp
  unfold LargeEvenSplit
  rw [ht]
  exact Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by decide, hdvd⟩)

theorem ggRootCompGenAvoiding_nbr_twE6ThreePlus (hRk : GGTwE6ThreeNbrRankInput)
    (hKG : GGTwE6ThreePlusKGAvoid) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K)
    (hK : GGInnerDiagOnLabel (fun p lab => GGTwE6BadLabel p lab ∧ 2 ≤ lab.n) p Bs K) :
    GGRootCompGenAvoiding p Bs K := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨hKy, -⟩ := isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hcfg.2.2 hnb)
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hKc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTwE6BadLabel p lab ∧ 2 ≤ lab.n)
    (P' := fun R _ I _ => GGTorusRootGenAvoidKG 3 5 R I)
    (fun lab _ hs => TwE6Delta.labelAll hs.1.1
      (fun K _ _ hK => hKG K lab.n hs.2 hK hs.1.2.2))
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, hInd⟩, hT3⟩ := largeEvenRawDatum_exists hraw
  have hp3 : p = 3 := hs.1.2.1
  have hKLab : GGInnerDiagOnLab GGTwE6BadLabel p Bs K :=
    largeEvenMarking_mono (fun lab R _ I F θ hP =>
      ⟨hP.1.1, l05nTRT_largeEvenSplit_of_twE6BadLabel hP.1.1, hP.2.1, hP.2.2⟩) hK
  subst hp3
  have hsc3 : GGTorusSelfCent 3 (ggGamma K hBsN).range :=
    ggTorusSelfCent_ggGamma hBsN hSC
  have hr : 3 ^ 5 ≤ Nat.card (ggGamma K hBsN).range :=
    hRk G 3 B Bs x L D J hcfg rfl y K hnb hKLab hBsN hsc3
  exact ggRootCompGenAvoiding_of_marking_avoidKG hp hp2 hBs hSC hyBs hKy.2.1 hKc θ hBsN
    (fun b hb => ggLAut_mem_of_induces K θ hBsN hInd hb)
    hr (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN) hT3

theorem ggRootGenNbrInputOnQFour_twE6ThreePlus (hRk : GGTwE6ThreeNbrRankInput)
    (hKG : GGTwE6ThreePlusKGAvoid) :
    GGRootGenNbrInputOnQFour fun p lab => GGTwE6BadLabel p lab ∧ 2 ≤ lab.n :=
  fun _ _ _ _ _ _ _ _ _ _ hHyp _ _ _ _ hnb hK =>
    ggRootCompGenAvoiding_nbr_twE6ThreePlus hRk hKG hHyp.1 hnb hK

end CFSG.StandardType

end
