module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09d
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09g
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09q
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R922A5
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09Shape92A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09h
import CFSG.LocalAnalysis.UniquenessCase.UCFront09l
import CFSG.LocalAnalysis.UniquenessCase.UCFront09m
import CFSG.LocalAnalysis.UniquenessCase.UCFront09n
import CFSG.LocalAnalysis.UniquenessCase.UCFront09o
import CFSG.LocalAnalysis.UniquenessCase.UCFront09p
import CFSG.LocalAnalysis.UniquenessCase.UCFront09r
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.AGLEmbedding (KFactCatalogSchreier)

variable {G : Type} [Group G] [Finite G]

theorem exists_hyp97_of_mem_calY2_9 (D : Data G) {X D₃ : Subgroup G} (hX : X ∈ calY2_9 D)
    (hD₃X : D₃ ≤ Opp 3 X) (hD₃ : Nat.card D₃ = 3) :
    ∃ Y H S : Subgroup G, X ≤ Y ∧ Hyp97 D Y H D₃ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Y, hXY, hY⟩ := Finite.exists_le_maximal (p := (· ∈ calY2_9 D)) hX
  have hY2 : Y ∈ calY2_9 D := hY.prop
  obtain ⟨N, hN, hNM⟩ : ∃ N ∈ calMOf Y, N ≠ D.M := by
    by_contra! h
    exact hY2.2.1 (Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, hY2.1.1⟩, h⟩)
  have hH := mem_calH2_9_of_mem_calMOf D hY2 hN hNM
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 Y
  have hXY3 : Opp 3 X ≤ Opp 3 Y := closure_mono fun x hx => ⟨hXY hx.1, hx.2⟩
  exact ⟨Y, N, S, hXY, ⟨hY2.1, hH.1, hD₃X.trans hXY3, hD₃⟩, hY, hH, hS⟩

theorem uniqueMax_of_r923K1 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hSch : KFactCatalogSchreier) (D : Data G) (hM : IsStronglyPEmbedded 3 D.M)
    (hE3 : R922A5 D) {L X : Subgroup G} (hLM : L ≤ D.M)
    (hLN : D.M ≤ normalizer (L : Set G)) (hA5 : IsAlt (Bar2 L) 5)
    (hUM : UniqueMax D.M (L ⊔ D.T)) (hX : Opp 3 X = X) (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L)
    (hZ : ⁅pCoreOf 2 D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) ⊓ X, X⁆ ≠ ⊥) :
    UniqueMax D.M X := by
  by_contra hMX
  obtain ⟨D₃, hD₃X, hD₃⟩ := exists_card_eq_three hXL hcov hA5
  obtain ⟨Y, H, S, hXY, h97⟩ := exists_hyp97_of_mem_calY2_9 D
    (mem_calY2_9_of_strong3 hG3 hSch D hM hLM hLN hXL hcov hA5 hX hMX)
    (hD₃X.trans hX.symm.le) hD₃
  have hYM : Y ≤ D.M := h97.1.1.1
  obtain ⟨hA5Y, hYL⟩ := isAlt_bar2_opp_of_pRank_le_one (hYM.trans hLN) hA5 hX hXL hcov hXY
    ((CFSG.SectionRank.pRank_mono (by norm_num) (opp_le_L9 Y H)).trans h97.1.2.1.2.2.le)
  exact hE3 Y H D₃ S h97 hA5Y (pCoreOf_ne_bot_of_le_of_commutator_ne_bot hYM hXY hZ)
    (not_isSylowOf_of_mem_calY2_9 D hLM hLN hUM hXL hcov hXY h97.2.1.prop h97.2.2.2.le)
    (calCGS_pCoreOf_le D (r910_holds D) hLM hLN hUM hcov hXY h97.2.1 hYL)

theorem r923K1_holds
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hSch : KFactCatalogSchreier)
    (hKF : KFactShape92NoFaithfulA5) (D : Data G) (h92 : R92 D) (hE3 : R922A5 D) :
    R923K1 D := by
  intro hk L _ hLM hLN hA5 hUM X hX hXL hcov hZ
  haveI := D.standing.simple
  have hM : IsStronglyPEmbedded 3 D.M := by
    by_contra h
    have := D.k_eq_two_iff.2 h
    omega
  have hXM : X ≤ D.M := hXL.trans hLM
  have hMtop : D.M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1
  have hUX := uniqueMax_of_r923K1 hG3 hSch D hM hE3 hLM hLN hA5 hUM hX hXL hcov hZ
  obtain ⟨D₃, hD₃X, hD₃⟩ := exists_card_eq_three hXL hcov hA5
  have hU3 : ∀ A : Subgroup G, A ≤ X → Nat.card A = 3 → A ∈ uniqueSet D.M := fun A hAX hA3 =>
    uc22p22r_mem_uniqueSet_of_sp D Nat.prime_three hM (hAX.trans hXM)
      (IsPGroup.of_card (n := 1) (hA3.trans (pow_one 3).symm)) (by rintro rfl; simp at hA3)
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
        mem_calH9_of_strong3 hG3 hSch D hM hLM hXL hcov hA5 hX hH.1.1 hXH hHM',
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
