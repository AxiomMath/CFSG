module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankDerive
public import CFSG.LocalAnalysis.StandardType.GGMaxRankJBridge
public import CFSG.LocalAnalysis.StandardType.GGMaxRankJWitness
public import CFSG.LocalAnalysis.StandardType.GGMaxRankNotLeviLE3
public import CFSG.LocalAnalysis.StandardType.GGMaxRankRowNonLevi
public import CFSG.LocalAnalysis.StandardType.GGMaxRankSide
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
import CFSG.LocalAnalysis.StandardType.GGMaxRankE8LiftHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggMaxRank_rowOther {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X Y J : Subgroup G} (hLab : GGLabelRigidInput)
    (eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs))
    (hX : GGMaxRankSideChain p Bs X J eJ) (hrowX : GGResRowAt ggRowMaxRank p J X)
    (hY : GGResSideDatum p Bs Y J ∨ GGResLeviSideDatumLE3 p Bs Y J ∨ GGResRowAt ggRowNonLevi p J Y) :
    GGResRowAt ggRowMaxRank p J Y := by
  rcases hY with hS | hL | hN
  · exact absurd hS (ggMaxRank_notLevi eJ hX)
  · exact absurd hL (ggMaxRank_notLeviLE3 eJ hX)
  · exact ggMaxRank_row_of_nonLevi hLab hrowX hN

theorem ggMaxRankOtherRow_of_tbjR
    (hCore : GGMaxRankE8Core) (hT : GGTBTorE8) (hLift : GGTBTorLiftE8)
    (hLab : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput) (hJR : GGTBJInputR)
    (hX : GGResXDichotomyInput) : GGMaxRankOtherRow := by
  intro G _ _ p B Bs x L D J y K hH _ hrow
  obtain ⟨hDL, hDK⟩ := ggResE8Separated_of_tbTor hT hLift hLab hH
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hJL : J ≤ L := hDJ.1.2.2.2.2.2.1.1.trans inf_le_left
  have hnbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hDJ y K hnbr
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hp3 : p = 3 := by
    rcases hrow with hr | hr <;>
    · obtain ⟨_, _, _, _, _, _, hmax⟩ := hr
      rcases hmax with ⟨-, h, -, -⟩ | ⟨-, h, -, -⟩ <;> exact h
  have hnt : ∀ X : Subgroup G, ∀ g ∈ ggAutomizer X Bs, ¬ GGIsTransvection p g := fun X =>
    ggNoTransvection_of_le_automizer hH.2.2.2.1 (ggAutomizer_mono Bs le_top)
  have hside : ∀ {X : Subgroup G}, GGInnerDiagOn Bs X → J ≤ X → GGResRowAt ggRowMaxRank p J X →
      GGResE8SeparatedDatum p Bs X →
      (∃ z ∈ Bs, z ∉ Subgroup.centralizer (X : Set G) ∧
        IsComponentOf J (X ⊓ Subgroup.centralizer ({z} : Set G))) →
      ∃ eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs), GGMaxRankSideChain p Bs X J eJ := by
    intro X hinn hJX hrowX hDX hw
    obtain ⟨eJ, heJ⟩ := ggMaxRankJReflection_side_of_core hLab hCore hH.1.2.1 hinn hJX hrowX hDX hw
    exact ⟨eJ, ggMaxRank_sideChain hp3 hp2 hBs hDX (hnt X) eJ heJ (ggAutomizer_mono Bs hJX)⟩
  have hnoSeven : ∀ {X : Subgroup G}, ¬ GGResRowAt ggRowSeven p J X := by
    intro X h
    obtain ⟨_, _, _, _, _, _, hp7, -⟩ := h
    omega
  have hLK : GGResRowAt ggRowMaxRank p J L → GGResRowAt ggRowMaxRank p J K := by
    intro hrL
    obtain ⟨eJ, hXL⟩ := hside hH.2.2.1.1 hJL hrL (hDL hrL) (ggMaxRank_witness hH hLab hrL)
    have hdat : GGResXDatum p Bs K := (hX G p B Bs x L D J y K hH).2.resolve_right hnoSeven
    exact ggMaxRank_rowOther hLab eJ hXL hrL ((hJR G p B Bs x L D J y K hH).2 hdat)
  have hKL : GGResRowAt ggRowMaxRank p J K → GGResRowAt ggRowMaxRank p J L := by
    intro hrK
    obtain ⟨eJ, hXK⟩ := hside (hH.2.2.1.2 y K hnbr) hJK hrK (hDK hrK) (ggMaxRank_witnessK hH hJK)
    have hdat : GGResXDatum p Bs L := (hX G p B Bs x L D J y K hH).1.resolve_right hnoSeven
    exact ggMaxRank_rowOther hLab eJ hXK hrK ((hJR G p B Bs x L D J y K hH).1 hdat)
  rcases hrow with hr | hr
  · exact ⟨hr, hLK hr⟩
  · exact ⟨hKL hr, hr⟩

theorem ggResMaxRankModelInput_of_inputs_tbjR
    (hCore : GGMaxRankE8Core) (hT : GGTBTorE8) (hLab : GGLabelRigidInput)
    (hI3 : GGNbrSubcomponentInput) (hJR : GGTBJInputR) (hX : GGResXDichotomyInput) :
    GGResMaxRankModelInput :=
  ggResMaxRankModelInput_of_inputs hCore hT ggTBTorLiftE8 hLab hI3
    (ggMaxRankOtherRow_of_tbjR hCore hT ggTBTorLiftE8 hLab hI3 hJR hX)

end CFSG.StandardType

end
