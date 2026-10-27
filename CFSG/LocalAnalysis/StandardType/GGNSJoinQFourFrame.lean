module

public import CFSG.LocalAnalysis.StandardType.GGResidualRk1Frame
public import CFSG.LocalAnalysis.StandardType.GGResidualGenFrame
public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourExact
public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourTop
public import CFSG.LocalAnalysis.StandardType.GGNSJoinLinGlue
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakPosDefs
public import Certificates.Certificate13604
public import Certificates.Certificate13605
public import Certificates.Certificate13691
public import Certificates.Certificate13720
public import Certificates.Certificate13721
public import Certificates.Certificate13722
public import Certificates.Certificate13723
public import Certificates.Certificate13724
public import Certificates.Certificate709545
public import Certificates.Certificate709548
public import Certificates.Certificate709549
public import Certificates.Certificate709590
import CFSG.LocalAnalysis.StandardType.GGNSJoinWeakOrthPosD
import CFSG.LocalAnalysis.StandardType.GGResidualGenFrameRest
import CFSG.LocalAnalysis.StandardType.GGResidualRk1FrameRest
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanUnitaryAnyA
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalInvolution.Phan


theorem GGRk1ResidualFrameInputExOf.rk1ConclEx_base {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hRig : GGLabelRigidInput) (hRk : GGTwE6ThreeNbrRankInput) (hU62 : GGU62OuterDiagInput) (hFix : GGTBFixInput)
    (hWA : GGTBFixNbrXInput) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hWI : GGNbrInnerWeylInput)
    (hTCJ : GGTCJKnown) (h : GGRk1ResidualFrameInputExOf T) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hU : ¬ GGMemberUnitary p Bs L) :
    ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs L r := by
  have hA : ¬ (GGIsWeylMatrixA M ∧
      ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) := by
    rintro ⟨⟨_, _, _, hM⟩, hbig⟩
    exact hU (ggMemberUnitary_anyA hRk hU62 hFix hWA hLB hSP hcfg hns hpres hM hbig (Or.inl rfl) hns)
  exact h.apply hRig hRk hFix hWA hU62 hLB hSP hWI hTCJ hcfg hns hpres h3 hA (Or.inl rfl) hns hU
    fun hLL => absurd rfl hLL

namespace NSJoin

theorem nsQFourInputOf_of_frame {T T' T'' : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hRig : GGLabelRigidInput) (hD : PhanDInput2) (hPE : PhanEInput2) (hRk : GGTwE6ThreeNbrRankInput)
    (hU62 : GGU62OuterDiagInput) (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) (hWI : GGNbrInnerWeylInput) (hTCJ : GGTCJKnown) (hRk1F : GGRk1ResidualFrameInputExOf T')
    (hGenF : GGGenResidualFrameInputOf T'') : NSQFourInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hreg
  by_cases hU : GGMemberUnitary p Bs L
  · exact nsQFourRow_uniOrd hT hRig G p B Bs x L D J 𝒦 hreg hU
  · obtain ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩ := hreg
    have h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := hT hTM
    obtain ⟨r₀, hA, hC⟩ :=
      hGenF.baseRefl hD hPE hRk hU62 hFix hWA hLB hSP hWI hTCJ G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig
    obtain ⟨F, hFfield, hFfin, θ, hchar, hinj, hrange, -, -, -, -, lab, hΛ, hhas, hFcard⟩ :=
      hRk1F.rk1ConclEx_base hRig hRk hU62 hFix hWA hLB hSP hWI hTCJ hcfg hns hpres h3 hU r₀ hA hC
    letI : Field F := hFfield
    letI : Finite F := hFfin
    have hcard : Nat.card ↥(ggRankOneIn L Bs r₀) = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [← hrange, ← ggSL2_card F]
      exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    have hguard := hbig r₀ hA hC
    rw [hcard, hFcard] at hguard
    have hn1 : 1 ≤ lab.n := hΛ.1
    have hn2 : 2 ≤ lab.n := by
      by_contra hlt
      have : lab.n = 1 := by omega
      rw [this] at hguard
      exact hguard (by norm_num)
    exact largeEvenMarking_mono (fun lab' _ _ _ _ _ ⟨he, hP⟩ => ⟨by
        unfold GGLabQFour; rw [he]; exact hn2, hP⟩)
      (ggInnerDiagOn_relabel hRig hcfg.1.2.2.1.1 hΛ hhas)

theorem nsWeakOrthPosInputOf_D_of_frame {T' T'' : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hKn : GGTCJEnnolaKnown) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) (hTP : GGNbrTablePNbrInputOn GGRegimeFieldTwo) (hBig : GGTwE6BigLabelsKnown)
    (hRk : GGTwE6ThreeNbrRankInput) (hD : PhanDInput2) (hPE : PhanEInput2) (hU62 : GGU62OuterDiagInput)
    (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput) (hWI : GGNbrInnerWeylInput)
    (hRk1F : GGRk1ResidualFrameInputExOf T') (hGenF : GGGenResidualFrameInputOf T'') :
    NSWeakOrthPosInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M) :=
  nsWeakOrthPosInputOf_D hRk
    (nsNbrQFourInputOf_of_types hRig hTCJ hLB hSP hTP hBig hRk (nsNbrLinearInput_holds hRig hTCJ hKn hLB hSP)
      (nsQFourInputOf_of_frame (fun h => h.le_three) hRig hD hPE hRk hU62 hFix hWA hLB hSP hWI hTCJ hRk1F hGenF)).2

theorem nsNbrQFourInputOf_E_of_frame {T' T'' : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hKn : GGTCJEnnolaKnown) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) (hTP : GGNbrTablePNbrInputOn GGRegimeFieldTwo) (hBig : GGTwE6BigLabelsKnown)
    (hRk : GGTwE6ThreeNbrRankInput) (hD : PhanDInput2) (hPE : PhanEInput2) (hU62 : GGU62OuterDiagInput)
    (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput) (hWI : GGNbrInnerWeylInput)
    (hRk1F : GGRk1ResidualFrameInputExOf T') (hGenF : GGGenResidualFrameInputOf T'') :
    NSNbrQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => GGIsWeylMatrixE M) :=
  nsNbrQFourInputOf_of_parts (fun h => h.le_three) hRig hTCJ hLB hSP hTP hBig hRk
    (nsNbrLinearInput_holds hRig hTCJ hKn hLB hSP)
    (nsQFourInputOf_of_frame (fun h => h.le_three) hRig hD hPE hRk hU62 hFix hWA hLB hSP hWI hTCJ hRk1F hGenF)

end NSJoin

end CFSG.StandardType

end
