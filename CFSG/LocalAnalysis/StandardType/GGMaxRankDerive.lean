module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankSide
public import CFSG.LocalAnalysis.StandardType.GGMaxRankDatum
public import CFSG.LocalAnalysis.StandardType.GGMaxRankJReflection
import CFSG.LocalAnalysis.StandardType.GGMaxRankJBridge
public import CFSG.LocalAnalysis.StandardType.GGMaxRankE8Typed
public import CFSG.LocalAnalysis.StandardType.GGResMaxRankModel
public import CFSG.LocalAnalysis.StandardType.GGCoxReflConv
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGMaxRankOtherRow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGResRowAt ggRowMaxRank p J L ∨ GGResRowAt ggRowMaxRank p J K) →
      GGResRowAt ggRowMaxRank p J L ∧ GGResRowAt ggRowMaxRank p J K

theorem ggResMaxRankModelInput_of_inputs
    (hCore : GGMaxRankE8Core) (hT : GGTBTorE8) (hLift : GGTBTorLiftE8)
    (hLab : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput) (hOther : GGMaxRankOtherRow) :
    GGResMaxRankModelInput := by
  have hJ := ggMaxRankJReflectionInputTyped_of_core hLab hCore
  intro G _ _ p B Bs x L D J y K hH _ hrow
  obtain ⟨hrL, hrK⟩ := hOther G p B Bs x L D J y K hH hrow
  obtain ⟨hDL, hDK⟩ := ggResE8Separated_of_tbTor hT hLift hLab hH
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hJL : J ≤ L := hDJ.1.2.2.2.2.2.1.1.trans inf_le_left
  obtain ⟨eJ, heJ⟩ := hJ G p B Bs x L D J y K hH hrL (hDL hrL)
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hp3 : p = 3 := by
    obtain ⟨_, _, _, _, _, _, hmax⟩ := hrL
    rcases hmax with ⟨-, h, -, -⟩ | ⟨-, h, -, -⟩ <;> exact h
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hDJ y K hH.2.2.2.2.1
  have hntL : ∀ g ∈ ggAutomizer L Bs, ¬ GGIsTransvection p g :=
    ggNoTransvection_of_le_automizer hH.2.2.2.1 (ggAutomizer_mono Bs le_top)
  have hntK : ∀ g ∈ ggAutomizer K Bs, ¬ GGIsTransvection p g :=
    ggNoTransvection_of_le_automizer hH.2.2.2.1 (ggAutomizer_mono Bs le_top)
  exact ggMaxRankDatum_mk eJ
    (ggMaxRank_sideChain hp3 hp2 hBs (hDL hrL) hntL eJ heJ (ggAutomizer_mono Bs hJL))
    (ggMaxRank_sideChain hp3 hp2 hBs (hDK hrK) hntK eJ heJ (ggAutomizer_mono Bs hJK))
    (GGConfig.card_bstar_inf_centralizer_L hH.1)

end CFSG.StandardType

end
