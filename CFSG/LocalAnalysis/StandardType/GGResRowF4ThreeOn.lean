module

public import CFSG.LocalAnalysis.StandardType.GGResXDatumOfWeylTypeCard
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeF4Three
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRank
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggF4Three_rank_of_innerDiagOnLabel
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hT : GGNoTransvection p Bs) {X : Subgroup G}
    (hM : GGInnerDiagOnLabel GGF4ThreeLabel p Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    p ^ 4 ≤ Nat.card (ggGamma X hN).range := by
  have hM' := hM
  obtain ⟨-, _, _, hraw⟩ := hM
  obtain ⟨_, _, _, _, _, _, _, hP, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, hp3, -⟩ := hP
  subst hp3
  exact ggF4Three_rank_of_marking (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds) hcfg
    hT hM' hN

theorem ggWeylTypeRankFamilyOn_f4Three
    : GGWeylTypeRankFamilyOn 4 GGF4ThreeLabel := by
  intro p hp hp2 lab hlab hT
  obtain ⟨ht, rfl, h3⟩ := hT
  exact ggF4ThreeNbrWeylTypeInput_holds lab hlab ⟨ht, rfl, h3⟩

theorem ggRankLOn_f4Three
    : GGRankLOn 4 GGF4ThreeLabel := by
  intro G _ _ p _ B Bs x L D J hcfg hT hM hN
  exact ggF4Three_rank_of_innerDiagOnLabel hcfg hT hM hN

theorem ggRankNbrOn_f4Three
    : GGRankNbrOn 4 GGF4ThreeLabel := by
  intro G _ _ p _ B Bs x L D J hcfg hT y K _ hK hN
  exact ggF4Three_rank_of_innerDiagOnLabel hcfg hT hK hN

theorem ggTBXDatumResOn_of_f4Three
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTBXDatumResOn (fun p lab => S p lab ∧ ¬ GGF4ThreeLabel p lab)) :
    GGTBXDatumResOn S :=
  ggTBXDatumResOn_of_weylTypeCard ggWeylTypeRankFamilyOn_f4Three (by norm_num) ggRankLOn_f4Three
    ggRankNbrOn_f4Three hRig hcyc h

theorem ggPZNbrResDatumOn_of_f4Three
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGPZNbrResDatumOn (fun p lab => S p lab ∧ ¬ GGF4ThreeLabel p lab)) :
    GGPZNbrResDatumOn S :=
  ggPZNbrResDatumOn_of_weylTypeCard ggWeylTypeRankFamilyOn_f4Three (by norm_num)
    ggRankNbrOn_f4Three hRig hcyc h

end CFSG.StandardType

end
