module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BetaKer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BetaFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BetaRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BetaTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapBeta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c13beta_main_dParam_three : dParam 3 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

private theorem s16c13beta_main_dParam_seven : dParam 7 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

private theorem s16c13beta_main_k_le_two (D : Data G) : D.k ≤ 2 := by
  unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
  split_ifs <;> omega

private theorem s16c13beta_main_k_eq_one (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h3 : 3 ∈ D.sig) : D.k = 1 := by
  unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
  rw [if_pos (hSg.sig1_sp 3 (h1219 ▸ h3))]

theorem s16c13beta_k_lt_dParam (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    {p : ℕ} (hp : p = 3 ∨ p = 7) (hpσ : p ∈ D.sig) : D.k < dParam p := by
  have hk2 : D.k ≤ 2 := s16c13beta_main_k_le_two D
  rcases hp with rfl | rfl
  · have h1 := s16c13beta_main_k_eq_one D hSg h1219 hpσ
    rw [s16c13beta_main_dParam_three]
    omega
  · rw [s16c13beta_main_dParam_seven]
    omega

theorem s16c13beta_bounds_of_case4 (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D V₀ V L hV) {r : ℕ} (hr : 3 < r) (h4 : Case168_4With D V₀ V hV L r) :
    ((D.k + 1 : ℕ) : ℕ∞) < betaN D.k D.M V ∧ ((D.k + 1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
  obtain ⟨p, hp, h4At⟩ := h4
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  have hpσ : p ∈ D.sig := h4At.2.2
  have hk : D.k < dParam p := s16c13beta_k_lt_dParam D hSg h1219 hp hpσ
  have hHyp : Hyp16 D V₀ V := hc.setting.hyp16
  have hH : Hyp125 D V₀ V := hHyp.hyp125
  have h4card : Nat.card V₀ ≤ 4 := Sixteen21.card_le_four_of_hyp16 hHyp
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hFX, hF, hFn, hFY, hQ⟩ :=
    s16c13beta_family_data D hV hc hp hr h4At
  have hT := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hgood := s16c13beta_fam_good hT hp hr hk hind hinj hsup hrk hperm hFX hF hFn hFY hQ
  have hpts := s16c13beta_rank_pts hT hp hr hk hind hrk (by omega) hFX hF hFn hFY
  exact ⟨s16c13beta_betaN_lt D h61 hV hH h4card hpp hp2 hpσ hgood,
    s16c13beta_rMV_lt D h61 hV hH h4card hpp hp2 hpσ hpts⟩

theorem s16c13beta_bounds_of_case4_sub (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D V₀ V L hV) {r : ℕ} (hr : 3 < r) (h4 : Case168_4With D V₀ V hV L r) :
    ((D.k + 1 : ℕ) : ℕ∞) < betaN D.k D.M V ∧
      ((D.k + 1 : ℕ) : ℕ∞) < rMV D.M V - (mSub V₀ : ℕ∞) := by
  obtain ⟨hβ, hr'⟩ := s16c13beta_bounds_of_case4 D hSg h1219 h61 hV hc hr h4
  refine ⟨hβ, ?_⟩
  generalize rMV D.M V = x at hr' ⊢
  induction x using ENat.recTopCoe with
  | top => simp
  | coe n =>
    have h1 : D.k + 1 + mSub V₀ < n := by exact_mod_cast hr'
    rw [← ENat.coe_sub]
    exact_mod_cast (by omega : D.k + 1 < n - mSub V₀)

theorem s16GapBetaBound_holds (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1) (h61 : UC6.R6_1 D) :
    S16GapBetaBound D := by
  intro V L hV hc ⟨r, hr, h4⟩
  have h := s16c13beta_bounds_of_case4 D hSg (h1219 ⊥ V hc.setting.hyp16.hyp125) h61 hV hc hr h4
  simpa [mSub, rk_bot] using h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
