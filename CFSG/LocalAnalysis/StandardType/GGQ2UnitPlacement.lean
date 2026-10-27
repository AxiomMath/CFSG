module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitNormalizerAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSplit
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameAmbientDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.UnitPlacement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem unit_position
    (hrig : GGLabelRigidInput) (hP0 : AmbientMarkedOverTwo)
    (hD : UnitInnerDiagData) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hm : LargeEvenMarking (ggG0 3 B x L D J) (fun lab _ _ _ _ _ => lab.tag = .twA)) :
    ∃ r : ℕ, GGInnerDiagOnLabel (fun _ l => l = (⟨.twA, r + 1 - 1, 1⟩ : LargeEvenLabel)) 3 Bs
        (ggG0 3 B x L D J) ∧
      IsElemAbelian 3 Bs ∧ (∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) ∧
      ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer ((ggG0 3 B x L D J : Subgroup G) : Set G)) ∧
      3 ^ 4 ≤ Nat.card Bs ∧ (3 ∣ r + 1 → 3 ^ (r + 1 - 3) ≤ Nat.card Bs) := by
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
    · rw [h]; exact hn
    · rw [h]; exact hn
    · rw [h]; exact hn
    · rw [h]; exact hn
    all_goals
      have ht2 := congrArg LargeEvenLabel.tag h
      rw [htag] at ht2
      simp at ht2
  obtain ⟨t, r, n⟩ := labm
  obtain rfl : n = 1 := hn1
  obtain rfl : t = .twA := htag
  have hHmark : GGInnerDiagOn Bs (ggG0 3 B x L D J) := hS.1.2.2.2.2
  have hInnU : GGInnerDiagOnLabel (fun _ l => l = (⟨.twA, r, 1⟩ : LargeEvenLabel)) 3 Bs
      (ggG0 3 B x L D J) := ggInnerDiagOn_relabel hrig hHmark hlabm2 hhasm
  have hInnN : GGInnerDiagOnLabel (fun _ l => l = (⟨.twA, r + 1 - 1, 1⟩ : LargeEvenLabel)) 3 Bs
      (ggG0 3 B x L D J) := by
    simpa only [Nat.add_sub_cancel] using hInnU
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨hp3, hEab, -, -, hcard⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hThmI : GGThmIHyp 3 B x L := hS.1.1.1
  have hStar : LargeEvenSStar 3 B x L := hThmI.2.2.2.2.2.2.1
  have hStdType : LargeEvenStandardType 3 B x L := hThmI.2.2.2.2.2.2.2
  have hStdSub : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hC3 := not_dvd_card_centralizer_ggG0_of_stdSub hp3 hStar hStdType hStdSub
  have hrk : 3 ∣ r + 1 → 3 ^ (r + 1 - 3) ≤ Nat.card Bs := by
    intro h3
    obtain ⟨K, _, _, hK, hN4, hHp, θ, -, -⟩ := hD hInnN
    have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
    have hdq : (r + 1, 2 ^ 1) ≠ (3, 2) := by
      intro h
      have h1 := congrArg Prod.fst h
      simp only at h1
      omega
    have hlift : GGTorusLift 3 (ggUnitaryTorusRank 3 (r + 1))
        (LargeEvenProj (unitarySU 2 1 K (r + 1))) :=
      ggTorusLift_unitary hK' le_rfl (by omega) hdq Nat.prime_three (by norm_num)
    have h := pow_le_card_bstar_of_torusLift hcfg hHp θ hlift
    simpa [ggUnitaryTorusRank, h3] using h
  exact ⟨r, hInnN, hEab, hSC, hC3, hcard, hrk⟩

theorem placementCoreInputOn_unit_of_pieces
    (hrig : GGLabelRigidInput)
    (hP0 : AmbientMarkedOverTwo) (hD : UnitInnerDiagData) (hF : ExistsUnitFrame)
    (hR : UnitFrameRange) (hOcc : UnitComponentOccursIff) (hCent : UnitComponentCentEq)
    (hIn : UnitComponentInsideEq) (hMk : UnitComponentMarked) (ex : FrameKind → RawFrameData) :
    PlacementCoreInputOn (fun lab => lab.tag = .twA) (catalogueOf classicalCatalogue ex) := by
  intro G _ _ p B Bs x L D J hS hp hm
  subst hp
  obtain ⟨r, hInnN, hEab, hSC, hC3, hcard, hrk⟩ := unit_position hrig hP0 hD hS hm
  rcases unitPlacementCore_of_pieces hD hF hR hOcc hCent hIn hMk hInnN hEab hSC hC3 hcard hrk with
    hcore | hcore
  · refine ⟨.unitFull (r + 1), ?_⟩
    rw [ActualCoreFrame,
      catalogueOf_classical _ _ (show IsClassical (.unitFull (r + 1)) from trivial)]
    exact hcore
  · refine ⟨.unitHeart (r + 1), ?_⟩
    rw [ActualCoreFrame,
      catalogueOf_classical _ _ (show IsClassical (.unitHeart (r + 1)) from trivial)]
    exact hcore

theorem placementInputOn_unit_of_pieces
    (hrig : GGLabelRigidInput)
    (hP0 : AmbientMarkedOverTwo) (hD : UnitInnerDiagData) (hF : ExistsUnitFrame)
    (hR : UnitFrameRange) (hOcc : UnitComponentOccursIff) (hCent : UnitComponentCentEq)
    (hIn : UnitComponentInsideEq) (hMk : UnitComponentMarked) (hAct : AutomizerActEq)
    (hAmb : UnitAmbientTorusAut) (hAmbH : UnitAmbientTorusAutH) (hComp : UnitComponentTorusAut)
    (hCompH : UnitComponentTorusAutH) (hM4 : UnitBlockPerfect) (ex : FrameKind → RawFrameData) :
    PlacementInputOn (fun lab => lab.tag = .twA) (catalogueOf classicalCatalogue ex) := by
  intro G _ _ p B Bs x L D J hS hp hm
  subst hp
  obtain ⟨r, hInnN, hEab, hSC, hC3, hcard, hrk⟩ := unit_position hrig hP0 hD hS hm
  rcases unitPlacement_of_pieces hD hF hR hOcc hCent hIn hMk hAct hAmb hAmbH hComp hCompH hM4
      hInnN hEab hSC hC3 hcard hrk with hreal | hreal
  · refine ⟨.unitFull (r + 1), ?_⟩
    rw [ActualFrame,
      catalogueOf_classical _ _ (show IsClassical (.unitFull (r + 1)) from trivial)]
    exact hreal
  · refine ⟨.unitHeart (r + 1), ?_⟩
    rw [ActualFrame,
      catalogueOf_classical _ _ (show IsClassical (.unitHeart (r + 1)) from trivial)]
    exact hreal

end CFSG.StandardType.GGQ2Frame
