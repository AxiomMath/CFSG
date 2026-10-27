module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2SpNormalizerAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSplit
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameAmbientDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.SpPlacement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem inLambda2_C_of_BC {t : LargeEvenLieTag} {r n : ℕ} (ht : t = .B ∨ t = .C)
    (h : LargeEvenInLambda2 ⟨t, r, n⟩) : LargeEvenInLambda2 ⟨.C, r, n⟩ := by
  rcases ht with rfl | rfl <;> exact h

theorem hasLabel_C_of_BC {t : LargeEvenLieTag} {r n : ℕ} {R : Type} [Group R]
    (ht : t = .B ∨ t = .C) (h : GGHasLabel ⟨t, r, n⟩ R) : GGHasLabel ⟨.C, r, n⟩ R := by
  rcases ht with rfl | rfl <;> exact h

private theorem sp_position (hrig : GGLabelRigidInput) (hP0 : AmbientMarkedOverTwo)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hm : LargeEvenMarking (ggG0 3 B x L D J)
      (fun lab _ _ _ _ _ => (fun lab : LargeEvenLabel => lab.tag = .B ∨ lab.tag = .C) lab)) :
    ∃ r : ℕ, GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel .symplectic r) 3 Bs
        (ggG0 3 B x L D J) ∧
      IsElemAbelian 3 Bs ∧ (∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) ∧
      ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer ((ggG0 3 B x L D J : Subgroup G) : Set G)) ∧
      3 ^ 4 ≤ Nat.card Bs := by
  obtain ⟨lab, hn, hInn⟩ := hP0 hS
  obtain ⟨labm, hlabm2, hhasm, -, -, -, -, -, htag⟩ := largeEvenMarking_exists_hasLabel hm
  obtain ⟨lab', hlab'2, hhas', R', _, I', F', θ', hP'⟩ := largeEvenMarking_exists_hasLabel hInn
  have hl : lab' = lab := hP'.1
  subst hl
  have hiso := hrig lab' labm _ hlab'2 hlabm2 hhas' hhasm
  have hn1 : labm.n = 1 := by
    rcases hiso with h | ⟨-, -, -, hnn⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · rw [← h]; exact hn
    · rw [← hnn]; exact hn
    all_goals
      have ht2 := congrArg LargeEvenLabel.tag h
      rcases htag with ht | ht <;> rw [ht] at ht2 <;> simp at ht2
  obtain ⟨t, r, n⟩ := labm
  obtain rfl : n = 1 := hn1
  have hlabC2 : LargeEvenInLambda2 ⟨.C, r, 1⟩ := inLambda2_C_of_BC htag hlabm2
  have hhasC : GGHasLabel ⟨.C, r, 1⟩ (↥(ggG0 3 B x L D J) ⧸ Subgroup.center ↥(ggG0 3 B x L D J)) :=
    hasLabel_C_of_BC htag hhasm
  have hHmark : GGInnerDiagOn Bs (ggG0 3 B x L D J) := hS.1.2.2.2.2
  have hInnC : GGInnerDiagOnLabel (fun _ l => l = planeAmbientLabel .symplectic r) 3 Bs
      (ggG0 3 B x L D J) := ggInnerDiagOn_relabel hrig hHmark hlabC2 hhasC
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨hp3, hEab, -, -, hcard⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hThmI : GGThmIHyp 3 B x L := hS.1.1.1
  have hStar : LargeEvenSStar 3 B x L := hThmI.2.2.2.2.2.2.1
  have hStdType : LargeEvenStandardType 3 B x L := hThmI.2.2.2.2.2.2.2
  have hStdSub : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  exact ⟨r, hInnC, hEab, hSC, not_dvd_card_centralizer_ggG0_of_stdSub hp3 hStar hStdType hStdSub,
    hcard⟩

theorem placementCoreInputOn_sp_of_pieces (hrig : GGLabelRigidInput) (hP0 : AmbientMarkedOverTwo)
    (hD : SpInnerDiagData) (hF : ExistsSpFrame) (hLe : SpEleH) (hOcc : SpComponentOccursIff)
    (hCent : SpComponentCentEq) (hIn : SpComponentInsideEq) (hMk : SpComponentMarked)
    (ex : FrameKind → RawFrameData) :
    PlacementCoreInputOn (fun lab => lab.tag = .B ∨ lab.tag = .C)
      (catalogueOf classicalCatalogue ex) := by
  intro G _ _ p B Bs x L D J hS hp hm
  subst hp
  obtain ⟨r, hInnC, hEab, hSC, hC3, hcard⟩ := sp_position hrig hP0 hS hm
  obtain ⟨core⟩ := spPlacementCore_of_pieces hD hF hLe hOcc hCent hIn hMk (m := r) hInnC hEab hSC
    hC3 hcard
  exact ⟨.symp r, ⟨core⟩⟩

theorem placementInputOn_sp_of_pieces (hrig : GGLabelRigidInput) (hP0 : AmbientMarkedOverTwo)
    (hD : SpInnerDiagData) (hF : ExistsSpFrame) (hLe : SpEleH) (hOcc : SpComponentOccursIff)
    (hCent : SpComponentCentEq) (hIn : SpComponentInsideEq) (hMk : SpComponentMarked)
    (hCov : CoverComponents.AutomizerCoverEq) (hAmb : SpBlocks.SpAmbientTorusAut)
    (hComp : SpBlocks.SpComponentTorusAut) (hQ : SpBlocks.SpIsQuasisimpleYcode)
    (ex : FrameKind → RawFrameData) :
    PlacementInputOn (fun lab => lab.tag = .B ∨ lab.tag = .C)
      (catalogueOf classicalCatalogue ex) := by
  intro G _ _ p B Bs x L D J hS hp hm
  subst hp
  obtain ⟨r, hInnC, hEab, hSC, hC3, hcard⟩ := sp_position hrig hP0 hS hm
  obtain ⟨real⟩ := spPlacement_of_pieces hD hF hLe hOcc hCent hIn hMk hCov hAmb hComp hQ (m := r)
    hInnC hEab hSC hC3 hcard
  exact ⟨.symp r, ⟨real⟩⟩

end CFSG.StandardType.GGQ2Frame
