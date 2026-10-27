module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeAssembly
public import CFSG.LocalAnalysis.StandardType.GGRealNbrNSTwE6
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeVac
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeUnitary
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeUnitaryHyp
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeOrth
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSympLin
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlus
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeE6Two
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeTwE6
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeF4Three
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeUSixThree
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeTwE6Three
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitA
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitBC
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitD
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitE6Three
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitExc
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcSeven

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

namespace NSJoin

theorem nsPumpNbrInput_holds
    (hF4R : GGF4ThreeNbrRankInput) (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hR : GGTwE6ThreeNbrRankInput) (hTCJ : GGTCJKnown) (hTP : GGSecFiveA8TablePInput)
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) : NSPumpNbrInputOf T := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hZ : GGNbrBstarCenterInput :=
    ggNbrBstarCenterInput_of_centerPCyclic ggLabelCenterPCyclicInput_holds
  have hW := ggNbrTableBWeylTypeNonSplitOn_of_families ggNbrTableBWeylTypeNonSplitOn_vac
    ggNbrTableBWeylTypeNonSplitOn_unitary ggNbrTableBWeylTypeNonSplitOn_unitaryHyp
    ggNbrTableBWeylTypeNonSplitOn_orth ggNbrTableBWeylTypeNonSplitOn_sympLin
    ggNbrTableBWeylTypeNonSplitOn_excPlus ggNbrTableBWeylTypeNonSplitOn_e6Two
    ggNbrTableBWeylTypeNonSplitOn_twE6
  have hNS := ggNbrWeylTypeNonSplitInput_of_weylType hW hF4R hL hPJ
    ggF4ThreeNbrWeylTypeInput_holds ggUSixThreeNbrWeylTypeInput_holds
  have hFull := ggNbrWeylTypeNonSplitFull_of_rank hNS hR ggTwE6ThreeNbrWeylTypeInput_holds hRig hZ
  have hSplit := ggNbrTableBWeylTypeSplitInput_of_families ggNbrTableBWeylTypeSplitOn_typeA
    ggNbrTableBWeylTypeSplitOn_typeBC ggNbrTableBWeylTypeSplitOn_typeD
    ggNbrTableBWeylTypeSplitOn_exc ggNbrTableBWeylTypeSplitOn_e6Three
  have hC4 := ggNbrExcSevenReflInput_holds hRig hTCJ hTP
  intro G _ _ p B Bs x L D J 𝒦 hcfg y K hK
  have hcfg' : GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg.1
  have h : GGSecFiveRestHyp p B Bs x L D J := hcfg'.1
  have hHS := ggNbr_halfSplit_of_secFiveRest hraw hiso h hK
  by_cases hsp : LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GGNbrSplitLabel p lab)
  · exact ggNbrWeylReflGroup_of_halfSplit hSplit hRig h.1 h.2.2.2.1 hK (h.2.2.1.2 y K hK) hsp
      (hZ G p B Bs x L D J h y K hK)
  by_cases hq : LargeEvenMarking ↥K (fun lab _ _ _ _ _ => p ∣ (2 ^ lab.n) ^ 2 - 1)
  · exact hFull G p B Bs x L D J h y K hK hsp hq
  exfalso
  have hDisj : LargeEvenMarking ↥K (fun lab _ _ _ _ _ =>
      p ∣ (2 ^ lab.n) ^ 2 - 1 ∨ (p = 7 ∧ (lab = ⟨.A, 8, 1⟩ ∨ lab = ⟨.E6, 0, 1⟩))) :=
    ggMarking_mono_lab (fun lab _ _ _ _ _ hlab hP => largeEvenHalfSplit_dvd hlab hP) hHS
  rcases largeEvenMarking_or hDisj with hd | hex
  · exact hq hd
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, hp7, hl⟩ := largeEvenMarking_exists_hasLabel hex
  have hrefl : GGReflGenerated p (ggAutomizer K Bs) := hcfg'.2.1 y K hK
  refine hC4 G p B Bs x L D J h y K hK hp7 ?_ hrefl
  rcases hl with rfl | rfl
  · exact Or.inl hhas
  · exact Or.inr hhas

theorem nsRealNbrInput_holds
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hR : GGTwE6ThreeNbrRankInput)
    (hRig : GGLabelRigidInput) : NSRealNbrInputOf T := by
  intro G _ _ B Bs x L D J 𝒦 hcfg y K hnb hq
  have hcfg' : GGSecFiveRouteCfg' 3 B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg.1
  have hc : GGConfig 3 B Bs x L D J := hcfg'.1.1
  have hNT : GGNoTransvection 3 Bs := hcfg'.1.2.2.2.1
  have hX : K = L ∨ ∃ y, GGNbr 3 B x D J y K := Or.inr ⟨y, hnb⟩
  have h3 : GGInnerDiagOnLabel (fun p lab =>
      (GGLabQFour p lab ∧ lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) ∨
      ((GGLabQFour p lab ∧ GGNbrInner937U63Label p lab) ∨
        (GGLabQFour p lab ∧
          (¬ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) ∧ ¬ GGNbrInner937U63Label p lab)))) 3 Bs K :=
    GGInnerDiagOnLabel.mono_label (fun lab hl => by
      by_cases h6 : lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1
      · exact Or.inl ⟨hl, h6⟩
      · by_cases hU : GGNbrInner937U63Label 3 lab
        · exact Or.inr (Or.inl ⟨hl, hU⟩)
        · exact Or.inr (Or.inr ⟨hl, h6, hU⟩)) hq
  rcases h3.elim_or with h₁ | h₂
  · exact ggReflRealizedIn_three_twE6Nbr hR hRig hc hNT hnb (hcfg'.1.2.2.1.2 y K hnb) h₁
  rcases h₂.elim_or with h₂ | h₃
  · exact ggReflRealizedIn_three_U63 hLB hSP hc hNT rfl hX h₂
  · exact ggReflRealizedIn_three_of_rootSL2On
      (S := fun p lab => ¬ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) ∧ ¬ GGNbrInner937U63Label p lab)
      ggRealRootSL2On_three_offU63_offTwE6 hc hNT rfl hX h₃

end NSJoin

end CFSG.StandardType

end
