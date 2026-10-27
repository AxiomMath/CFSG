module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ln
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BetaMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Certified

theorem s16c1610_out10_of_no_calOStar (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hkm : D.k < mBar D.M V₀ V h.isElemAbelian)
    (hno : V₀ ≠ ⊥ → ∀ g : G, ¬ InCalOStar D.k D.M V₀ V g) :
    Out10 D V₀ V h.isElemAbelian := by
  refine ⟨hkm, fun hV₀ g hO1 => hno hV₀ g ?_⟩
  have hk := s16c1610_k_cases D
  have hH := s16c1610_hyp6H D hx h61 h127 h1114 h
  have hm1 : 1 < mBar D.M V₀ V h.isElemAbelian := by omega
  have hr : ((mSub V₀ + D.k : ℕ) : ℕ∞) < rMV D.M V := by
    have hW := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h hV₀
    have h1 := h162 D V₀ V hW hx h61 hV₀ hm1
    refine lt_of_lt_of_le ?_ h1
    exact_mod_cast (by omega : mSub V₀ + D.k < mBar D.M V₀ V h.isElemAbelian + mSub V₀)
  exact (hH.hyp65 hV₀ hO1).inCalOStar_of_lt_rMV hr

theorem s16c1610_out10_of_case4_big (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) {p r : ℕ} (hp : p = 3 ∨ p = 7)
    (hr : 3 < r) (h4At : Case168_4At D V₀ V hV L p r) (hkm : D.k < mBar D.M V₀ V hV) :
    Out10 D V₀ V hV := by
  have hb := s16c13beta_bounds_of_case4_sub D hin.hSg hin.h1219 hin.h61 hV hc hr ⟨p, hp, h4At⟩
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hpk : D.k + 1 < p := by
    rcases hp with rfl | rfl
    · have := Data.k_eq_one_of_three_mem D hin.hSg hin.h1219 h4At.2.2
      omega
    · have := s16c167_k_le_two D
      omega
  have hle : lBar V₀ V hV L ≤ pCoreOf p (Mbar D.M V₀ V hV) :=
    s16n9b_case4_pcore D hV hc hpp (by omega) h4At.1
  have hXne : pCoreOf p (Mbar D.M V₀ V hV) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hle
    exact hc.ne_bot (le_bot_iff.1 hle)
  have hXp : IsPGroup p ↥(pCoreOf p (Mbar D.M V₀ V hV)) :=
    CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf p _
  exact s16c1610_out10_of_r13 D hin.hx hin.h61 hin.h127 hin.h1114 hc.setting.hyp16.hyp125 hkm
    hpp hpk hXne (Subgroup.map_subtype_le _) hXp
    (fun m hm x hx => CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hm hx)
    (fun _ => hb.1) (fun _ => hb.2)

theorem s16c1610_out10_of_case2_four (D : Data G) (hin : In10 D) (h4 : 3 < CFSG.Open.evenRank G)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h2 : Case168_2Star D V₀ V hV L) : Out10 D V₀ V hV := by
  obtain ⟨hK, ⟨L₀, hdir, hshape⟩, hσ⟩ := h2
  rcases hshape with ⟨n, hn5, hn11, hS, -, hsum⟩ | ⟨m, hm3, hm5, hL₀, hL, hsum⟩ |
    ⟨hS, -, hsum⟩ | ⟨hO, hO', hsum⟩ | ⟨hO, hO', hsum⟩
  · exact s16c1610_out10_of_case2_sym D hin hc hK hσ hdir hn5 hn11 hS hsum
  · exact s16c1610_out10_of_case2_ln D hin hc hK hσ hdir hm3 hm5 (fun _ _ => h4) hL₀ hL hsum
  · exact s16c1610_out10_of_case2_sp D hin hc hK hσ hdir hS hsum
  · exact s16c1610_out10_of_case2_ominus_six D hin hc hK hσ hdir hO hO' hsum
  · exact s16c1610_out10_of_case2_ominus_eight D hin hc hK hσ hdir hO hO' hsum

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
