module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcPlacementDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2NoTwoNodeExc
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameAmbientDefs
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFIn2
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoverSelfCent
import CFSG.LocalAnalysis.StandardType.GGQ2ExcModelFrameCover
import CFSG.LocalAnalysis.StandardType.GGQ2ExcUntwCover
import CFSG.LocalAnalysis.StandardType.GGQ2ExcUntwFrameOrder

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.ExcPlacement

private theorem ker_rootMap_le_cent (m : Fin 6) (c : Finset (ExcRaw.Root m)) :
    LinearMap.ker (ExcRaw.rootMap m c) ≤ ExcRaw.cent m c := by
  intro v hv
  simp only [ExcRaw.cent, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i hi
  have h := congrFun (LinearMap.mem_ker.mp hv) i
  simpa [ExcRaw.rootMap, hi] using h

private theorem eq_of_labelIso_of_exceptional {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab')
    (hex : ExceptionalLabel lab') : lab = lab' := by
  rcases h with h | ⟨-, ht, -, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · rcases hex with h1 | h1 | h1 | h1 | h1 <;> rcases ht with h2 | h2 <;> rw [h1] at h2 <;>
      simp at h2
  all_goals
    have ht2 := congrArg LargeEvenLabel.tag h
    rcases hex with h1 | h1 | h1 | h1 | h1 <;> rw [h1] at ht2 <;> simp at ht2

private theorem rank_eq_zero_of_exceptional {lab : LargeEvenLabel} (h2 : LargeEvenInLambda2 lab)
    (hex : ExceptionalLabel lab) : lab.rank = 0 := by
  obtain ⟨t, r, n⟩ := lab
  rcases hex with h | h | h | h | h <;> (dsimp only at h; subst h; exact h2.2)

private noncomputable def coverEquiv {H M : Type} [Group H] [Group M] (π : H →* M)
    (hsurj : Function.Surjective π) (hker : π.ker = Subgroup.center H) :
    H ⧸ Subgroup.center H ≃* M :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hsurj)

private theorem exc_position (hrig : GGLabelRigidInput) (hP0 : AmbientMarkedOverTwo)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hm : LargeEvenMarking (ggG0 3 B x L D J) (fun lab _ _ _ _ _ => ExceptionalLabel lab)) :
    ∃ t : LargeEvenLieTag, ExceptionalLabel ⟨t, 0, 1⟩ ∧
      GGInnerDiagOnLabel (fun _ lab => lab = ⟨t, 0, 1⟩) 3 Bs (ggG0 3 B x L D J) ∧
      IsElemAbelian 3 Bs ∧ (∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) ∧
      ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer ((ggG0 3 B x L D J : Subgroup G) : Set G)) ∧
      3 ^ 4 ≤ Nat.card Bs := by
  obtain ⟨lab, hn, hInn⟩ := hP0 hS
  obtain ⟨labm, hlabm2, hhasm, -, -, -, -, -, hex⟩ := largeEvenMarking_exists_hasLabel hm
  obtain ⟨lab', hlab'2, hhas', R', _, I', F', θ', hP'⟩ := largeEvenMarking_exists_hasLabel hInn
  have hl : lab' = lab := hP'.1
  subst hl
  have heq : lab' = labm :=
    eq_of_labelIso_of_exceptional (hrig lab' labm _ hlab'2 hlabm2 hhas' hhasm) hex
  subst heq
  have hr := rank_eq_zero_of_exceptional hlab'2 hex
  obtain ⟨t, r, n⟩ := lab'
  dsimp only at hn hr
  subst hn hr
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨hp3, hEab, -, -, hcard⟩ := hcfg.tableB_facts
  have hThmI : GGThmIHyp 3 B x L := hS.1.1.1
  exact ⟨t, hex, hInn, hEab, hcfg.2.1.2.2.2,
    not_dvd_card_centralizer_ggG0_of_stdSub hp3 hThmI.2.2.2.2.2.2.1 hThmI.2.2.2.2.2.2.2 hS.1.1.2.2,
    hcard⟩

private theorem untw_frame (m : Fin 6) {τ : Tag} {r : ℕ} (hSCc : CoverSelfCent)
    (hMF : ModelFrameOfCover) (hOrd : ExcUntwFrameOrder τ r (ExcRaw.dim m))
    (hModel : ExcUntwModelFrame m τ) {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = (excRaw m).ambientLabel) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥H)) (hEH : E ≤ H) (hperf : commutator H = ⊤)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (π : ↥H →* adjointGroup τ K)
    (hsurj : Function.Surjective π) (hker : π.ker = Subgroup.center ↥H)
    (hcard : 3 ^ r ≤ Nat.card E) : ActualFrame H E (excRaw m) := by
  have hker3 : ¬ 3 ∣ Nat.card π.ker := by rw [hker]; exact hZ3
  obtain ⟨hE'ab, hE'card, hE'SC⟩ := hSCc hEH π hsurj hker.le hker3 hEab hSC
  have hE'ord := hOrd hK hE'ab hE'SC (by rw [hE'card]; exact hcard)
  obtain ⟨mf'⟩ := hModel hK hE'ab hE'ord hE'SC
  obtain ⟨mf⟩ := hMF hEH π hsurj hker.le hker3 hperf hEab mf'
  exact ⟨Realization.ofModelFrame mf hInn fun c _ => ker_rootMap_le_cent m c⟩

theorem placementInputOn_exc_of_pieces
    (hrig : GGLabelRigidInput) (hP0 : AmbientMarkedOverTwo)
    (hModF4 : ExcUntwModelFrame 0 .F4) (hModE6 : ExcUntwModelFrame 1 .E6)
    (hModE7 : ExcUntwModelFrame 4 .E7) (hModE8 : ExcUntwModelFrame 5 .E8)
    (hTw : ExcTwE6Placement) :
    PlacementInputOn ExceptionalLabel (catalogueOf classicalCatalogue excCatalogue) := by
  have hSCc : CoverSelfCent := coverSelfCent_holds
  have hMF : ModelFrameOfCover := modelFrameOfCover_holds
  have hCovF4 : ExcUntwCover .F4 .F4 := excUntwCover_F4_holds
  have hCovE6 : ExcUntwCover .E6 .E6 := excUntwCover_E6_holds
  have hCovE7 : ExcUntwCover .E7 .E7 := excUntwCover_E7_holds
  have hCovE8 : ExcUntwCover .E8 .E8 := excUntwCover_E8_holds
  have hLiftE7 : ExcUntwTorusLift .E7 6 := excUntwTorusLift_E7_holds
  have hLiftE8 : ExcUntwTorusLift .E8 7 := excUntwTorusLift_E8_holds
  have hOrdF4 : ExcUntwFrameOrder .F4 4 4 := excUntwFrameOrder_F4_holds
  have hOrdE6 : ExcUntwFrameOrder .E6 4 4 := excUntwFrameOrder_E6_holds
  have hOrdE7 : ExcUntwFrameOrder .E7 6 7 := excUntwFrameOrder_E7_holds
  have hOrdE8 : ExcUntwFrameOrder .E8 7 8 := excUntwFrameOrder_E8_holds
  intro G _ _ p B Bs x L D J hS hp hm
  subst hp
  obtain ⟨t, hex, hInn, hEab, hSC, hC3, hcard⟩ := exc_position hrig hP0 hS hm
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hZ3 := not_three_dvd_card_center_ggG0 hS
  have key : ∀ m : Fin 6, ActualFrame (ggG0 3 B x L D J) Bs (excRaw m) →
      ∃ kind : FrameKind, ActualFrame (ggG0 3 B x L D J) Bs
        (catalogueOf classicalCatalogue excCatalogue kind) := fun m h =>
    ⟨.exceptional m, by rw [catalogueOf_exceptional _ _ (k := .exceptional m) fun h => h]; exact h⟩
  rcases hex with ht | ht | ht | ht | ht <;> dsimp only at ht <;> subst ht
  · obtain ⟨hEH, hperf, K, _, _, hK, π, hsurj, hker⟩ := hCovF4 hInn hEab hC3
    exact key 0 (untw_frame 0 hSCc hMF hOrdF4 hModF4 hInn hEab hSC hZ3 hEH hperf hK π hsurj hker
      hcard)
  · obtain ⟨hEH, hperf, K, _, _, hK, π, hsurj, hker⟩ := hCovE6 hInn hEab hC3
    exact key 1 (untw_frame 1 hSCc hMF hOrdE6 hModE6 hInn hEab hSC hZ3 hEH hperf hK π hsurj hker
      hcard)
  · rcases hTw hS hInn with h | h
    · exact key 2 h
    · exact key 3 h
  · obtain ⟨hEH, hperf, K, _, _, hK, π, hsurj, hker⟩ := hCovE7 hInn hEab hC3
    exact key 4 (untw_frame 4 hSCc hMF hOrdE7 hModE7 hInn hEab hSC hZ3 hEH hperf hK π hsurj hker
      (pow_le_card_bstar_of_torusLift hcfg hperf (coverEquiv π hsurj hker) (hLiftE7 hK)))
  · obtain ⟨hEH, hperf, K, _, _, hK, π, hsurj, hker⟩ := hCovE8 hInn hEab hC3
    exact key 5 (untw_frame 5 hSCc hMF hOrdE8 hModE8 hInn hEab hSC hZ3 hEH hperf hK π hsurj hker
      (pow_le_card_bstar_of_torusLift hcfg hperf (coverEquiv π hsurj hker) (hLiftE8 hK)))

end CFSG.StandardType.GGQ2Frame
