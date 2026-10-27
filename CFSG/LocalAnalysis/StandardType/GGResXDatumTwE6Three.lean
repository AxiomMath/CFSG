module

public import CFSG.LocalAnalysis.StandardType.GGResXDatumOfWeylTypeCard
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwE6Bad_p_eq_three {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}
    (hL : GGInnerDiagOnLabel GGTwE6BadLabel p Bs L) : p = 3 := by
  obtain ⟨-, lab, -, hraw⟩ := hL
  obtain ⟨_, _, _, _, _, _, _, hP, -⟩ := largeEvenRawDatum_exists hraw
  exact hP.2.1

theorem ggInnerDiagOnLab_of_twE6Bad {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}
    (hM : GGInnerDiagOnLabel GGTwE6BadLabel p Bs L) :
    GGInnerDiagOnLab GGTwE6BadLabel p Bs L := by
  refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hM
  obtain ⟨⟨ht, hp3, hpn⟩, hBN, hBI⟩ := hP
  refine ⟨⟨ht, hp3, hpn⟩, Or.inr (Or.inl ⟨?_, ?_, by rw [hp3]; exact hpn⟩), hBN, hBI⟩
  · rw [ht]; exact fun h => h
  · rw [ht]; decide

theorem ggWeylTypeRankFamilyOn_twE6Three :
    GGWeylTypeRankFamilyOn 5 GGTwE6BadLabel := by
  intro p _ _ lab hlab hT
  obtain rfl : p = 3 := hT.2.1
  exact ggTwE6ThreeNbrWeylTypeInput_holds lab hlab hT

theorem ggRankLOn_twE6Three :
    GGRankLOn 5 GGTwE6BadLabel := by
  intro G _ _ p _ B Bs x L D J hcfg _ hL hN
  have hp3 : p = 3 := ggTwE6Bad_p_eq_three hL
  subst hp3
  have hM : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L :=
    (ggInnerDiagOnLab_of_twE6Bad hL).mono fun _ _ h => h
  exact ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hcfg hM hN

theorem ggRankNbrOn_twE6Three (hRk : GGTwE6ThreeNbrRankInput) : GGRankNbrOn 5 GGTwE6BadLabel := by
  intro G _ _ p _ B Bs x L D J hcfg _ y K hnb hK hN
  have hp3 : p = 3 := ggTwE6Bad_p_eq_three hK
  subst hp3
  exact hRk G 3 B Bs x L D J hcfg rfl y K hnb (ggInnerDiagOnLab_of_twE6Bad hK) hN
    (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2)

theorem ggTBXDatumResOn_of_twE6Three
    (hRk : GGTwE6ThreeNbrRankInput) (hRig : GGLabelRigidInput)
    (hcyc : GGLabelCenterPCyclicInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTBXDatumResOn (fun p lab => S p lab ∧ ¬ GGTwE6BadLabel p lab)) :
    GGTBXDatumResOn S :=
  ggTBXDatumResOn_of_weylTypeCard ggWeylTypeRankFamilyOn_twE6Three (by norm_num)
    ggRankLOn_twE6Three (ggRankNbrOn_twE6Three hRk) hRig hcyc h

theorem ggPZNbrResDatumOn_of_twE6Three
    (hRk : GGTwE6ThreeNbrRankInput) (hRig : GGLabelRigidInput)
    (hcyc : GGLabelCenterPCyclicInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGPZNbrResDatumOn (fun p lab => S p lab ∧ ¬ GGTwE6BadLabel p lab)) :
    GGPZNbrResDatumOn S :=
  ggPZNbrResDatumOn_of_weylTypeCard ggWeylTypeRankFamilyOn_twE6Three (by norm_num)
    (ggRankNbrOn_twE6Three hRk) hRig hcyc h


end CFSG.StandardType

end
