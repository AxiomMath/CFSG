module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL62Good
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL62Weight2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ExitsSetup
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7UseThree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Fusion
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K6a K6b K6c IsLie811)

variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem Ctx82E3.false_of_l62 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK6a : K6a) (hK6b : K6b)
    (hK6c : K6c) (hK332 : UCK.K332ThreeAb) (hKF7 : UC22.KF7Use D) (hCA : K7L6TwoCentA)
    (hPf : K7L6TwoPerfect) (hlie : IsLie811 c.Lbar .l6 2 1) (hZ : Subgroup.center c.Lbar = ⊥)
    (hsig : D.sig = {7}) : False := by
  obtain ⟨h⟩ := c.nonempty_case811Sylow_of_l62 h811 hK6a hK6b hlie hZ
  obtain ⟨s⟩ := Case811Sylow.SignedLift.nonempty h hK6c hlie (by intro hh; cases hh)
  have hP := h.card_P_of_l62 hlie hZ
  have h7 : 7 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 7
  obtain ⟨y, hy, hy7, hyL⟩ := h.exists_seven_of_l62 hCA hlie hZ h7
  have hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v) :=
    fun v hv hw => s.good_of_weight_one_or_three_of_l62 hPf hlie hKF7 h7 hy hy7 hyL hv hw
  have hdvdM : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      7 ∣ Nat.card (D.M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
    intro X hXA _
    obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyX : y ∈ D.M ⊓ Subgroup.centralizer (X : Set G) :=
      Subgroup.mem_inf.mpr ⟨hyM, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXA) hyC⟩
    rw [← hy7, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hyX)
  have h100 : (![1, 0, 0] : Fin 3 → ZMod 3) ≠ 0 := by decide
  have hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M :=
    h.normalizer_A_le_of_dvdM h7 hdvdM (s.pt_mem_A ![1, 0, 0]) (s.orderOf_pt h100)
      (hgood _ h100 (Or.inr ⟨0, by decide⟩))
  have hall : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      Subgroup.normalizer (X : Set G) ≤ D.M ∧
        7 ∣ Nat.card (Subgroup.normalizer (X : Set G)) := by
    intro X hXA hXc
    refine ⟨?_, (hdvdM X hXA hXc).trans (Subgroup.card_dvd_of_le
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))⟩
    obtain ⟨v, hv0, rfl⟩ := s.exists_pt_of_card_three hXA hXc
    exact s.good_of_ne_zero_of_l62 hK332 hCA hlie hP h7 hy hy7 hgood hNA hv0
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact h.not_rankThreeGamma_le
    (CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le (p := 7) (q := 3)
      (M := D.M) (A := h.A) (c.isStronglyPEmbedded_of_mem_sigma h7) h.elemAbelian.isPGroup hall)

theorem l62ExcludedSetup_of_inputs (hK6a : K6a) (hK6b : K6b) (hK6c : K6c)
    (hK332 : UCK.K332ThreeAb) (hSQ : Section7.StronglyEmbeddedSolvableQ)
    (hSE5 : Section7.StronglyEmbeddedFive) (hSE3 : Section7.StronglyEmbeddedThree)
    (hZ6 : ∀ (Y : Type) [Group Y] [Finite Y], IsLie811 Y .l6 2 1 → Subgroup.center Y = ⊥)
    (hCA : K7L6TwoCentA) (hPf : K7L6TwoPerfect) : L62ExcludedSetup := by
  intro G _ _ hS _ _ S _ c h811 hlie hsig
  exact c.false_of_l62 h811 hK6a hK6b hK6c hK332 (UC22.kf7Use_dataOfSetup hSQ hSE5 hSE3 hS S)
    hCA hPf hlie (hZ6 _ hlie) hsig

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
