module
public import CFSG.LocalAnalysis.StandardType.GGOriginalTwE6TwoNoncommPairLeaf
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6ToralCoordsHolds
public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourExact
public import CFSG.LocalAnalysis.StandardType.GGResLineJCells
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1FrameHolds
import CFSG.LocalAnalysis.StandardType.GGNsq2U62
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylInputHolds
import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc11R
import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrHolds
import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGResidualRk1ExcTops
public import Certificates.Certificate27014
public import Certificates.Certificate27015
public import Certificates.Certificate27582
public noncomputable section
namespace CFSG.StandardType
open CFSG.Assembly CFSG.Open CFSG.GroupTheory CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

theorem ggTwE6Two_original_rankOne_of_route_proved
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie 3 L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦)
    (hXns : ¬ GGSplitLie 3 X) (hXnu : ¬ GGMemberUnitary 3 Bs X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) 3 Bs X) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx 3 Bs X r := by
  have hQ := NSJoin.nsNbrQFourInputOf_E_holds
  have hRig := ggLabelRigidInput_holds
  have hRk := ggTwE6ThreeNbrRankInput_holds
  have hFix := ggTBFixInput_holds
  have hWA := ggTBFixNbrXInput_holds
  have hU62 := ggU62OuterDiagInput_holds
  have hLB := ggLBalanceInput_holds
  have hSP := ggStdSubPrimeInput_holds
  have hWI := ggNbrInnerWeylInput_holds
  have hTCJ := TCJ.ggTCJKnown_holds
  have hXw : X = L ∨ GGSecFiveWeakNbr 3 B Bs x L D J 𝒦 X :=
    hX.imp_right (GGSecFiveWeakNbr.of_mem hcfg)
  have hNoAD : ¬ (GGIsWeylMatrixA M ∨ NSJoin.NSTypeD M) := fun hAD =>
    ggResidual_excRow_absurd_AD hRig hRk hcfg hpres hle3 hAD hXw
      (hmark.mono' fun _ h => Or.inl h.1)
  have hA : ¬ GGIsWeylMatrixA M := fun h => hNoAD (Or.inl h)
  have hD : ¬ NSJoin.NSTypeD M := fun h => hNoAD (Or.inr h)
  have hE : GGIsWeylMatrixE M := GGIsWeylMatrixE.of_not_typeA_not_typeD hpres.1 hle3 hA hD
  have hX' : X = L ∨
      (X ∈ 𝒦 ∧ ¬ (NSJoin.NSTypeD M ∧
        ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)) ∨
      (GGIsWeylMatrixE M ∧
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) ∧
        GGSecFiveWeakNbr 3 B Bs x L D J 𝒦 X) := by
    rcases hX with hXL | hK
    · exact Or.inl hXL
    · exact Or.inr (Or.inl ⟨hK, fun h => hD h.1⟩)
  have hQ4X : X ≠ L → ¬ NSJoin.NSTypeD M →
      (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
      3 = 3 → GGInnerDiagOnLabel GGLabQFour 3 Bs X := by
    intro hXL _ hbig _
    have hK : X ∈ 𝒦 := hX.resolve_left hXL
    exact NSJoin.innerDiagOnLabel_qFour_of_nbrQFour_E hQ hcfg hns hpres hE hbig
      (Or.inl hK)
  exact (ggRk1ResidualFrameInputExOf_holds (T := GGIsWeylMatrixE)
    hRig hRk hFix hWA hU62 hLB hSP hWI hTCJ).apply
      hRig hRk hFix hWA hU62 hLB hSP hWI hTCJ
      hcfg hns hpres hle3 (fun h => hA h.1) hX' hXns hXnu hQ4X


theorem ggTwE6Two_original_pair_of_route_proved
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L Dj J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L Dj J 𝒦) (hns : ¬ GGSplitLie 3 L)
    {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦)
    (hXns : ¬ GGSplitLie 3 X) (hXnu : ¬ GGMemberUnitary 3 Bs X)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) 3 Bs X)
    {r s : MulAut Bs} (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e)
    (hsA : s ∈ ggAutomizer X Bs) (hsC : s ∈ ggCoxRefl M e)
    (hne : r ≠ s) : GGPairConcl Bs X r s := by
  let S : ℕ → LargeEvenLabel → Prop := fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1
  have hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1 :=
    fun _ h => h.1
  let D := twE6CoverData hS hmark
  have hn1 : D.lab.n = 1 := D.hSlab.2
  have hmark1 : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X := by
    refine ggInnerDiagOnLabel_mono_lambda2 (fun lab hΛ h => ?_) hmark
    rcases lab with ⟨tag, rank, n⟩
    rcases h with ⟨⟨ht, _⟩, hn⟩
    change tag = .twE6 at ht
    change n = 1 at hn
    subst tag
    subst n
    have hzero : rank = 0 := hΛ.2
    subst rank
    rfl
  have hBs : IsElemAbelian 3 Bs := hcfg.1.1.2.1.2.1
  let := D.fieldK
  let := D.finiteK
  obtain ⟨κ, hκ⟩ := exists_twE6ToralCoords_of_route_proved hcfg hX hS hmark
  change TwE6ToralCoords D.lab.n D.hEN D.ψ κ at hκ
  let : Fact (IsElemAbelian 3 Bs) := ⟨hBs⟩
  have hr := ggCoxRefl_isReflection hpres.2 hrC
  have hs := ggCoxRefl_isReflection hpres.2 hsC
  have hR : GGRk1ConclEx 3 Bs X r :=
    ggTwE6Two_original_rankOne_of_route_proved hcfg hns hpres hle3 hX hXns hXnu hmark r hrA hrC
  let D1 := GGFinModel.original_qTwo_cover_view D hn1 hmark1
  have hκ1 : TwE6ToralCoords 1 D.hEN D.ψ κ := by simpa only [hn1] using hκ
  have hfree := D1.twoKernelInG_inf_centralizer_eq_bot hR hκ1 hrA hr hsA hs
  refine ⟨?_, ?_⟩
  · intro hcomm
    obtain ⟨α, β, hα, hβ, hHr, hHs, hiff⟩ := hκ1.exists_roots_ggHyperplane_iff hrA hr hsA hs
    have hrI : r ∈ ggInduced ⊤ Bs := by
      obtain ⟨g, -, hg, hrg⟩ := mem_ggAutomizer_iff.mp hrA
      exact ⟨g, trivial, hg, hrg⟩
    have hsI : s ∈ ggInduced ⊤ Bs := by
      obtain ⟨g, -, hg, hsg⟩ := mem_ggAutomizer_iff.mp hsA
      exact ⟨g, trivial, hg, hsg⟩
    have hH : ggHyperplane Bs r ≠ ggHyperplane Bs s := fun h =>
      hne (ggReflection_eq_of_ggHyperplane_eq (by decide) hBs hcfg.1.2.2.2.1 hr hs hrI hsI h)
    have hβα : β ≠ α := fun h => hH (hiff.mp (Or.inl h))
    have hβa : β ≠ -α := fun h => hH (hiff.mp (Or.inr h))
    have hαnβ : α ≠ -β := by
      intro h
      exact hβa (by simpa only [neg_neg] using congrArg Neg.neg h.symm)
    have horth := hκ1.iform_eq_zero_of_original_reflections_commute hα hβ (Ne.symm hβα) hαnβ
      (hκ1.act_eq_excRefl_of_ggHyperplane_iff hrA hr hα hHr)
      (hκ1.act_eq_excRefl_of_ggHyperplane_iff hsA hs hβ hHs) hcomm
    exact GGFinModel.original_qTwo_residuals_commute_of_same_cover D hn1 hmark1 hBs hκ
      r s α β hα hβ horth hHr hHs hfree
  · intro hrs
    exact GGOriginalTwE6TwoNoncommPairInput_holds G X Bs S hS hmark D hn1 hmark1 hBs κ
      hκ hcfg.1.2.2.2.1 r s hrA hr hsA hs hR hrs

end CFSG.StandardType
