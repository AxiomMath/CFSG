module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09s
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Cyc
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UCFront09v
import CFSG.LocalAnalysis.UniquenessCase.UCFront09h
import CFSG.LocalAnalysis.UniquenessCase.UCFront09l
import CFSG.LocalAnalysis.UniquenessCase.UCFront09m
import CFSG.LocalAnalysis.UniquenessCase.UCFront09n
import CFSG.LocalAnalysis.UniquenessCase.UCFront09o
import CFSG.LocalAnalysis.UniquenessCase.UCFront09p
import CFSG.LocalAnalysis.UniquenessCase.UCFront09r
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.AGLEmbedding (KFactCatalogSchreier)

variable {G : Type} [Group G] [Finite G]

theorem mem_calY2_9_of_pRank_le_three (hK : UCK.K332Cyc) (D : Data G)
    (h3 : CFSG.Open.pRank 3 D.M ≤ 3) {L X : Subgroup G} (hLM : L ≤ D.M)
    (hLN : D.M ≤ normalizer (L : Set G)) (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L)
    (hA5 : IsAlt (Bar2 L) 5)
    (hU3 : ∀ A : Subgroup G, A ≤ X → Nat.card A = 3 → A ∈ uniqueSet D.M) (hX : Opp 3 X = X)
    (hMX : calMOf X ≠ {D.M}) : X ∈ calY2_9 D := by
  have := D.standing.simple
  have hXM : X ≤ D.M := hXL.trans hLM
  refine ⟨⟨hXM, calNOf_ne_of_calMOf_ne D hXM hMX, hU3⟩, hMX, fun N hN => ?_, fun A hA => ?_,
    ⟨0, ?_⟩⟩
  · by_cases hNM : N = D.M
    · exact Or.inr hNM
    · exact Or.inl (mem_calH9_of_pRank_le_three hK D h3 hLN hXL hcov hA5 hU3 hX
        (CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1.1) hN.2
        (not_le_of_mem_calMOf D hN hNM))
  · rw [hX]
    exact commutator_le_pCoreOf_of_mem_inv9' hLN hXL hcov hA5 hA
  · rw [hX, Subgroup.subgroupOf_self, Subgroup.index_top, pow_zero]

theorem uniqueMax_of_pRank_le_three (hK : UCK.K332Cyc) (D : Data G)
    (h3 : CFSG.Open.pRank 3 D.M ≤ 3) (hE3 : R922A5 D) {L X : Subgroup G} (hLM : L ≤ D.M)
    (hLN : D.M ≤ normalizer (L : Set G)) (hA5 : IsAlt (Bar2 L) 5)
    (hUM : UniqueMax D.M (L ⊔ D.T))
    (hU3 : ∀ A : Subgroup G, A ≤ X → Nat.card A = 3 → A ∈ uniqueSet D.M) (hX : Opp 3 X = X)
    (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L)
    (hZ : ⁅pCoreOf 2 D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) ⊓ X, X⁆ ≠ ⊥) :
    UniqueMax D.M X := by
  by_contra hMX
  obtain ⟨D₃, hD₃X, hD₃⟩ := exists_card_eq_three hXL hcov hA5
  obtain ⟨Y, H, S, hXY, h97⟩ := exists_hyp97_of_mem_calY2_9 D
    (mem_calY2_9_of_pRank_le_three hK D h3 hLM hLN hXL hcov hA5 hU3 hX hMX)
    (hD₃X.trans hX.symm.le) hD₃
  have hYM : Y ≤ D.M := h97.1.1.1
  obtain ⟨hA5Y, hYL⟩ := isAlt_bar2_opp_of_pRank_le_one (hYM.trans hLN) hA5 hX hXL hcov hXY
    ((CFSG.SectionRank.pRank_mono (by norm_num) (opp_le_L9 Y H)).trans h97.1.2.1.2.2.le)
  exact hE3 Y H D₃ S h97 hA5Y (pCoreOf_ne_bot_of_le_of_commutator_ne_bot hYM hXY hZ)
    (not_isSylowOf_of_mem_calY2_9 D hLM hLN hUM hXL hcov hXY h97.2.1.prop h97.2.2.2.le)
    (calCGS_pCoreOf_le D (r910_holds D) hLM hLN hUM hcov hXY h97.2.1 hYL)

theorem r923_holds
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hSch : KFactCatalogSchreier)
    (hKF : KFactShape92NoFaithfulA5) (hK : UCK.K332Cyc) (D : Data G)
    (hSg : UC6S846.SigmaStd D) (h92 : R92 D) (hE3 : R922A5 D) : R923 D := by
  intro L hL hLM hLN hA5 hUM hSyl X hX hXL hcov hZ
  by_cases hM : IsStronglyPEmbedded 3 D.M
  · exact r923K1_holds hG3 hSch hKF D h92 hE3
      (by unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam; rw [if_pos hM])
      L hL hLM hLN hA5 hUM X hX hXL hcov hZ
  have := D.standing.simple
  have h3 : CFSG.Open.pRank 3 D.M ≤ 3 := by
    by_contra h
    exact hM (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL)
      (hSg.four_mem 3 Nat.prime_three (by norm_num) (by omega)))
  have hXM : X ≤ D.M := hXL.trans hLM
  have hMtop : D.M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1
  have hcovL : L = L ⊔ pCoreOf 2 L :=
    (sup_eq_left.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).symm
  have hU3 : ∀ A : Subgroup G, A ≤ X → Nat.card A = 3 → A ∈ uniqueSet D.M := fun A hAX hA3 =>
    hSyl A (isSylowOf_of_card_eq_three le_rfl hcovL hA5 (hAX.trans hXL) hA3)
  have hUX := uniqueMax_of_pRank_le_three hK D h3 hE3 hLM hLN hA5 hUM hU3 hX hXL hcov hZ
  obtain ⟨D₃, hD₃X, hD₃⟩ := exists_card_eq_three hXL hcov hA5
  have hND : ∀ A : Subgroup G, A ≤ X → Nat.card A = 3 → normalizer (A : Set G) ≤ D.M :=
    fun A hAX hA3 => normalizer_le_of_mem_uniqueSet D.maxLocal (hU3 A hAX hA3)
  have hP2 : ∀ H ∈ calNOf X, H = D.M := by
    intro H hH
    by_contra hHM
    have hXH : X ≤ H := hH.2
    have hO2 := pCoreOf_eq_bot_of_mem_calNOf D hUX hH hHM
    have hHM' : ¬ H ≤ D.M := fun h =>
      hHM ((eq_or_lt_of_le h).resolve_right fun hlt => hMtop (hH.1.2 _ hlt))
    have h91 : Hyp91 D X H D₃ :=
      ⟨⟨hXM, fun h => hHM (by rw [h] at hH; exact hH), hU3⟩,
        mem_calH9_of_pRank_le_three hK D h3 hLN hXL hcov hA5 hU3 hX hH.1.1 hXH hHM',
        hD₃X.trans hX.symm.le, hD₃⟩
    obtain ⟨R, hR⟩ := exists_mem_invStar9 (I9 H ⊔ X) X 2
    obtain ⟨-, hNR, -, hRI⟩ := isSylowOf_of_mem_invStar9 D hLM hLN hA5 hXL hcov hZ hUX hXH hR
    have hE := rankThreeLayer_I9_le D.standing.kProper hH.1.1 hO2 hRI (le_normalizer.trans hNR)
      (hD₃X.trans hXH) hD₃ ((centralizer_le_normalizer _).trans (hND D₃ hD₃X hD₃))
    have hO := relPPrimeCore_two_I9_le hLM hXL hcov hA5 hX hZ hUX hND hXH
    exact false_of_le_centralizer_I9 hKF hLM hA5 hX hXL hcov hZ hXH
      (le_centralizer_I9 hLN hXL hcov hA5 hX hXH hO2 hO hE) (h92 X H D₃ h91 hH.1.1).2
  obtain ⟨N, hN, hMN⟩ := (eq_top_or_exists_le_coatom D.M).resolve_left hMtop
  have hNX : N ∈ calNOf X := ⟨hN, hXM.trans hMN⟩
  exact Set.eq_singleton_iff_unique_mem.2 ⟨hP2 N hNX ▸ hNX, hP2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
