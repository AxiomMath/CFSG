module

public import CFSG.LocalAnalysis.StandardType.GGRootGenResQFourDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggRootGenNbrInputOnQFour_f4ThreePlus (hRk : GGF4ThreeNbrRankInput)
    (hKG : GGF4ThreePlusKGAvoid) :
    GGRootGenNbrInputOnQFour fun p lab => GGF4ThreeLabel p lab ∧ 2 ≤ lab.n := by
  unfold GGRootGenNbrInputOnQFour
  intro G _ _ p B Bs x L D J hHyp hq hN y K hnb hK
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨hKy, -⟩ := isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hcfg.2.2 hnb)
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hNoT : GGNoTransvection p Bs := hHyp.2.2.2.1
  obtain ⟨hKc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGF4ThreeLabel p lab ∧ 2 ≤ lab.n)
    (P' := fun R _ I _ => GGTorusRootGenAvoidKG 3 4 R I)
    (fun lab _ hs => by
      obtain ⟨⟨htag, -, hdvd⟩, hn⟩ := hs
      obtain ⟨t, l, n⟩ := lab
      dsimp only at htag hdvd hn
      subst htag
      intro Q hQ
      obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      haveI : CharP K 2 := charP_two_of_card hK
      have h4 : 4 ≤ Nat.card K := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have hd : 3 ∣ Nat.card K + 1 := by rw [hK]; exact hdvd
      exact ⟨K, inferInstance, inferInstance, hK, hQ', hKG K h4 hd⟩)
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, hInd⟩, hT3⟩ := largeEvenRawDatum_exists hraw
  have hp3 : p = 3 := hs.1.2.1
  have hKLab : GGInnerDiagOnLabel GGF4ThreeLabel p Bs K :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hP.1.1, hP.2.1, hP.2.2⟩) hK
  subst hp3
  have hsc3 : GGTorusSelfCent 3 (ggGamma K hBsN).range :=
    ggTorusSelfCent_ggGamma hBsN hSC
  have hr : 3 ^ 4 ≤ Nat.card (ggGamma K hBsN).range :=
    hRk G 3 B Bs x L D J hcfg hNoT rfl y K hnb hKLab hBsN hsc3
  exact ggRootCompGenAvoiding_of_marking_avoidKG hp hp2 hBs hSC hyBs hKy.2.1 hKc θ hBsN
    (fun b hb => ggLAut_mem_of_induces K θ hBsN hInd hb)
    hr (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN) hT3

end CFSG.StandardType

end
