module

public import CFSG.LocalAnalysis.StandardType.GGRootGenResQFourDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggRootCompGenAvoiding_L_resL (hRk : GGTwE6ThreeBstarRankInput)
    (hKG : GGTwE6ThreePlusKGAvoid) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLabel GGRootGenResLLabel p Bs L) : GGRootCompGenAvoiding p Bs L := by
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hLx : IsSubnormal L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hLab : GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs L :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => by
      obtain ⟨⟨ht, hp3, -, hd⟩, hBsN, hind⟩ := hP
      exact ⟨⟨ht, hp3, hd⟩,
        Or.inr (Or.inl ⟨by rw [ht]; simp [LargeEvenUntwisted], by rw [ht]; decide,
          by rw [hp3]; exact hd⟩), hBsN, hind⟩) hL
  obtain ⟨hLc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGRootGenResLLabel p lab)
    (P' := fun R _ I _ => GGTorusRootGenAvoidKG 3 5 R I)
    (fun lab hlab hs => by
      obtain ⟨ht, -, hn2, hd⟩ := hs
      exact TwE6Delta.labelAll ht fun K _ _ hK => hKG K lab.n hn2 hK hd)
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, h3⟩, hT⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, hp3, -, -⟩ := hs
  have hr : 3 ^ 5 ≤ Nat.card (ggGamma L hBsN).range :=
    hRk G p B Bs x L D J hcfg hLab hBsN
  have h3' : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range := le_trans (by norm_num) hr
  have hr5 : p ^ 5 ≤ Nat.card (ggGamma L hBsN).range := by rw [hp3]; exact hr
  have h3p : p ^ 3 ≤ Nat.card (ggGamma L hBsN).range := by rw [hp3]; exact h3'
  have hTp : GGTorusRootGenAvoidKG p 5 R I := by rw [hp3]; exact hT
  exact ggRootCompGenAvoiding_of_marking_avoidKG hp hp2 hBs hSC hxBs hLx hLc θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hr5 h3p hTp

theorem ggRootGenLInputOnQFour_resL (hRk : GGTwE6ThreeBstarRankInput)
    (hKG : GGTwE6ThreePlusKGAvoid) : GGRootGenLInputOnQFour GGRootGenResLLabel :=
  fun _ _ _ _ _ _ _ _ _ _ hHyp _ _ hL => ggRootCompGenAvoiding_L_resL hRk hKG hHyp.1 hL

end CFSG.StandardType

end
