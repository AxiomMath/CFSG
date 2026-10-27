module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthNormalizerAssembly
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
open CFSG.StandardType.GGQ2Frame.OrthPlacement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_planeAmbientLabel_orthogonal {tg : LargeEvenLieTag} {r : ℕ}
    (ht : tg = .D ∨ tg = .twD) (h2 : LargeEvenInLambda2 ⟨tg, r, 1⟩) :
    ∃ (t : ℕ) (δ : Fin 2),
      (⟨tg, r, 1⟩ : LargeEvenLabel) = planeAmbientLabel (.orthogonal δ) t := by
  rcases ht with rfl | rfl
  · have hr : 3 ≤ r := h2.2
    rcases Nat.even_or_odd r with he | ho
    · exact ⟨r, 0, by simp [planeAmbientLabel, he]⟩
    · have he : Even (r - 1) := by
        obtain ⟨k, hk⟩ := ho
        exact ⟨k, by omega⟩
      refine ⟨r - 1, 1, ?_⟩
      simp [planeAmbientLabel, he]
      omega
  · have hr : 2 ≤ r := h2.2
    rcases Nat.even_or_odd r with he | ho
    · have ho' : ¬ Even (r - 1) := by
        rw [Nat.not_even_iff_odd]
        obtain ⟨k, hk⟩ := he
        exact ⟨k - 1, by omega⟩
      refine ⟨r - 1, 1, ?_⟩
      simp [planeAmbientLabel, ho']
      omega
    · exact ⟨r, 0, by simp [planeAmbientLabel, Nat.not_even_iff_odd.mpr ho]⟩

private theorem orth_position (hrig : GGLabelRigidInput) (hP0 : AmbientMarkedOverTwo)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hm : LargeEvenMarking (ggG0 3 B x L D J)
      (fun lab _ _ _ _ _ => lab.tag = .D ∨ lab.tag = .twD)) :
    ∃ (t : ℕ) (δ : Fin 2),
      GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel (.orthogonal δ) t) 3 Bs
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
    rcases hiso with h | ⟨-, ht2, -, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · rw [← h]; exact hn
    · rcases htag with ht | ht <;> rcases ht2 with ht2 | ht2 <;> rw [ht] at ht2 <;> simp at ht2
    · have ht2 := congrArg LargeEvenLabel.tag h
      rcases htag with ht | ht <;> rw [ht] at ht2 <;> simp at ht2
    · have h2 : labm.n = lab'.n := by rw [h]
      omega
    · have ht2 := congrArg LargeEvenLabel.tag h
      rcases htag with ht | ht <;> rw [ht] at ht2 <;> simp at ht2
    · have h2 : labm.n = lab'.n := by rw [h]
      omega
    · have ht2 := congrArg LargeEvenLabel.tag h
      rcases htag with ht | ht <;> rw [ht] at ht2 <;> simp at ht2
    · have h2 : lab'.n = 2 * labm.n := congrArg LargeEvenLabel.n h
      omega
  obtain ⟨tg, r, n⟩ := labm
  obtain rfl : n = 1 := hn1
  obtain ⟨t, δ, hlab⟩ := exists_planeAmbientLabel_orthogonal htag hlabm2
  have hlabO2 : LargeEvenInLambda2 (planeAmbientLabel (.orthogonal δ) t) := hlab ▸ hlabm2
  have hhasO : GGHasLabel (planeAmbientLabel (.orthogonal δ) t)
      (↥(ggG0 3 B x L D J) ⧸ Subgroup.center ↥(ggG0 3 B x L D J)) := hlab ▸ hhasm
  have hHmark : GGInnerDiagOn Bs (ggG0 3 B x L D J) := hS.1.2.2.2.2
  have hInnO : GGInnerDiagOnLabel (fun _ l => l = planeAmbientLabel (.orthogonal δ) t) 3 Bs
      (ggG0 3 B x L D J) := ggInnerDiagOn_relabel hrig hHmark hlabO2 hhasO
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨hp3, hEab, -, -, hcard⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hThmI : GGThmIHyp 3 B x L := hS.1.1.1
  have hStar : LargeEvenSStar 3 B x L := hThmI.2.2.2.2.2.2.1
  have hStdType : LargeEvenStandardType 3 B x L := hThmI.2.2.2.2.2.2.2
  have hStdSub : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hC3 := not_dvd_card_centralizer_ggG0_of_stdSub hp3 hStar hStdType hStdSub
  exact ⟨t, δ, hInnO, hEab, hSC, hC3, hcard⟩

theorem placementCoreInputOn_orth_of_pieces (hrig : GGLabelRigidInput)
    (hP0 : AmbientMarkedOverTwo) (hD : OrthInnerDiagData) (hF : ExistsOrthFrame)
    (hLe : OrthEleH) (hSm : OrthSmallRankVacuous) (hOcc : OrthComponentOccursIff)
    (hCent : OrthComponentCentEq) (hIn : OrthComponentInsideEq) (hMk : OrthComponentMarked)
    (ex : FrameKind → RawFrameData) :
    PlacementCoreInputOn (fun lab => lab.tag = .D ∨ lab.tag = .twD)
      (catalogueOf classicalCatalogue ex) := by
  intro G _ _ p B Bs x L D J hS hp hm
  subst hp
  obtain ⟨t, δ, hInnO, hEab, hSC, hC3, hcard⟩ := orth_position hrig hP0 hS hm
  by_cases h4 : 4 ≤ t + δ.val
  · obtain ⟨core⟩ := orthPlacementCore_of_pieces hD hF hLe hOcc hCent hIn hMk hInnO hEab hSC
      hC3 hcard h4
    exact ⟨.orth t δ, ⟨core⟩⟩
  · exact absurd hcard (not_le.mpr (hSm hInnO (by omega) hEab hSC hC3))

theorem placementInputOn_orth_of_pieces (hrig : GGLabelRigidInput)
    (hP0 : AmbientMarkedOverTwo) (hD : OrthInnerDiagData) (hF : ExistsOrthFrame)
    (hLe : OrthEleH) (hSm : OrthSmallRankVacuous) (hOcc : OrthComponentOccursIff)
    (hCent : OrthComponentCentEq) (hIn : OrthComponentInsideEq) (hMk : OrthComponentMarked)
    (hCov : CoverComponents.AutomizerCoverEq) (hAmb : OrthBlocks.OrthAmbientTorusAut)
    (hComp : OrthBlocks.OrthComponentTorusAut) (hQ : OrthBlocks.OrthIsQuasisimpleYcode)
    (ex : FrameKind → RawFrameData) :
    PlacementInputOn (fun lab => lab.tag = .D ∨ lab.tag = .twD)
      (catalogueOf classicalCatalogue ex) := by
  intro G _ _ p B Bs x L D J hS hp hm
  subst hp
  obtain ⟨t, δ, hInnO, hEab, hSC, hC3, hcard⟩ := orth_position hrig hP0 hS hm
  by_cases h4 : 4 ≤ t + δ.val
  · obtain ⟨real⟩ := orthPlacement_of_pieces hD hF hLe hOcc hCent hIn hMk hCov hAmb hComp hQ
      (t := t) (δ := δ) hInnO hEab hSC hC3 hcard h4
    exact ⟨.orth t δ, ⟨real⟩⟩
  · exact absurd hcard (not_le.mpr (hSm hInnO (by omega) hEab hSC hC3))

end CFSG.StandardType.GGQ2Frame
