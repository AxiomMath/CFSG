module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2LinNormalizerAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSplit
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameAmbientDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.LinPlacement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem lin_position (hrig : GGLabelRigidInput) (hP0 : AmbientMarkedOverTwo)
    (hV : LinA1FourVacuous) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hm : LargeEvenMarking (ggG0 3 B x L D J)
      (fun lab _ _ _ _ _ => (fun lab : LargeEvenLabel => lab.tag = .A) lab)) :
    ∃ r : ℕ, GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, 1⟩) 3 Bs (ggG0 3 B x L D J) ∧
      IsElemAbelian 3 Bs ∧ (∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) ∧
      ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer ((ggG0 3 B x L D J : Subgroup G) : Set G)) ∧
      3 ^ 4 ≤ Nat.card Bs := by
  obtain ⟨lab, hn, hInn⟩ := hP0 hS
  obtain ⟨labm, hlabm2, hhasm, -, -, -, -, -, htag⟩ := largeEvenMarking_exists_hasLabel hm
  obtain ⟨lab', hlab'2, hhas', R', _, I', F', θ', hP'⟩ := largeEvenMarking_exists_hasLabel hInn
  have hl : lab' = lab := hP'.1
  subst hl
  have hiso := hrig lab' labm _ hlab'2 hlabm2 hhas' hhasm
  have hHmark : GGInnerDiagOn Bs (ggG0 3 B x L D J) := hS.1.2.2.2.2
  have hInnm : GGInnerDiagOnLabel (fun _ l => l = labm) 3 Bs (ggG0 3 B x L D J) :=
    ggInnerDiagOn_relabel hrig hHmark hlabm2 hhasm
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨hp3, hEab, -, -, hcard⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hThmI : GGThmIHyp 3 B x L := hS.1.1.1
  have hStar : LargeEvenSStar 3 B x L := hThmI.2.2.2.2.2.2.1
  have hStdType : LargeEvenStandardType 3 B x L := hThmI.2.2.2.2.2.2.2
  have hStdSub : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hC3 := not_dvd_card_centralizer_ggG0_of_stdSub hp3 hStar hStdType hStdSub
  have hcases : labm.n = 1 ∨ labm = ⟨.A, 1, 2⟩ := by
    rcases hiso with h | ⟨-, -, -, hnn⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inl (by rw [← h]; exact hn)
    · exact Or.inl (by rw [← hnn]; exact hn)
    · exact Or.inl (by rw [h]; exact hn)
    · have ht2 := congrArg LargeEvenLabel.tag h
      rw [htag] at ht2
      simp at ht2
    · have ht2 := congrArg LargeEvenLabel.tag h
      rw [htag] at ht2
      simp at ht2
    · have ht2 := congrArg LargeEvenLabel.tag h
      rw [htag] at ht2
      simp at ht2
    · exact Or.inr (by rw [h, hn])
    · have ht2 := congrArg LargeEvenLabel.tag h
      rw [htag] at ht2
      simp at ht2
  rcases hcases with hn1 | hA14
  · obtain ⟨tg, r, n⟩ := labm
    obtain rfl : n = 1 := hn1
    obtain rfl : tg = .A := htag
    exact ⟨r, hInnm, hEab, hSC, hC3, hcard⟩
  · rw [hA14] at hInnm
    exact absurd hcard (hV hInnm hEab hC3)

theorem exists_planes (r : ℕ) : ∃ (t : ℕ) (ε : Fin 2), 2 * t + ε.val = r + 1 :=
  ⟨(r + 1) / 2, ⟨(r + 1) % 2, Nat.mod_lt _ two_pos⟩, Nat.div_add_mod (r + 1) 2⟩

theorem placementCoreInputOn_lin_of_pieces (hrig : GGLabelRigidInput)
    (hP0 : AmbientMarkedOverTwo) (hD : LinInnerDiagData) (hV : LinA1FourVacuous)
    (hF : ExistsLinFrame) (hLe : LinEleH) (hOcc : LinComponentOccursIff)
    (hCent : LinComponentCentEq) (hIn : LinComponentInsideEq) (hMk : LinComponentMarked)
    (ex : FrameKind → RawFrameData) :
    PlacementCoreInputOn (fun lab => lab.tag = .A) (catalogueOf classicalCatalogue ex) := by
  intro G _ _ p B Bs x L D J hS hp hm
  subst hp
  obtain ⟨r, hInn, hEab, hSC, hC3, hcard⟩ := lin_position hrig hP0 hV hS hm
  obtain ⟨t, ε, hrt⟩ := exists_planes r
  obtain ⟨core⟩ := linPlacementCore_of_pieces hD hF hLe hOcc hCent hIn hMk hrt hInn hEab hSC
    hC3 hcard
  refine ⟨.lin t ε, ?_⟩
  rw [ActualCoreFrame, catalogueOf_classical _ _ (show IsClassical (.lin t ε) from trivial)]
  exact ⟨core⟩

theorem placementInputOn_lin_of_pieces (hrig : GGLabelRigidInput) (hP0 : AmbientMarkedOverTwo)
    (hD : LinInnerDiagData) (hV : LinA1FourVacuous) (hF : ExistsLinFrame) (hLe : LinEleH)
    (hOcc : LinComponentOccursIff) (hCent : LinComponentCentEq) (hIn : LinComponentInsideEq)
    (hMk : LinComponentMarked) (hCov : CoverComponents.AutomizerCoverEq)
    (hAmb : LinBlocks.LinAmbientTorusAut) (hComp : LinBlocks.LinComponentTorusAut)
    (hQ : LinBlocks.LinIsQuasisimpleYcode) (ex : FrameKind → RawFrameData) :
    PlacementInputOn (fun lab => lab.tag = .A) (catalogueOf classicalCatalogue ex) := by
  intro G _ _ p B Bs x L D J hS hp hm
  subst hp
  obtain ⟨r, hInn, hEab, hSC, hC3, hcard⟩ := lin_position hrig hP0 hV hS hm
  obtain ⟨t, ε, hrt⟩ := exists_planes r
  obtain ⟨real⟩ := linPlacement_of_pieces hD hF hLe hOcc hCent hIn hMk hCov hAmb hComp hQ hrt
    hInn hEab hSC hC3 hcard
  refine ⟨.lin t ε, ?_⟩
  rw [ActualFrame, catalogueOf_classical _ _ (show IsClassical (.lin t ε) from trivial)]
  exact ⟨real⟩

end CFSG.StandardType.GGQ2Frame
