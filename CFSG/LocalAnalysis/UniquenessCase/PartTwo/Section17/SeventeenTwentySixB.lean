module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenSetting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c2Gt2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem seventeen_twentysix_b_three_of_ne (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_25 : R17_25At D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Gt2 G) (hV0 : V₀ ≠ ⊥) :
    ∀ L : Subgroup G, (c : Ctx17_17 D V₀ V L) →
      (4 + mSub V₀ : ℕ∞) ≤ rMV D.M V := by
  intro L c
  have h25 := h17_25 L c
  obtain ⟨-, -, hm4, -⟩ := h25
  have hsetting : WeakClosureSetting D V₀ V :=
    weakClosureSetting_of_hyp125 D hx h61 h127 h1114 c.hyp125 hV0
  have hm : 2 < mBar D.M V₀ V c.hyp125.isElemAbelian := by omega
  have h := h162 D V₀ V hsetting hV0 hm
  rw [hm4] at h
  exact_mod_cast h


theorem seventeen_twentysix_b_three (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_25 : R17_25At D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Gt2 G) (h111 : W3Thm111 G) :
    R17_26b_3At D V₀ V := by
  intro L c
  rcases eq_or_ne V₀ ⊥ with hV0 | hV0
  · subst hV0
    have h25 := h17_25 L c
    have hm4 : mBar D.M ⊥ V c.hyp125.isElemAbelian = 4 := h25.2.2.1
    have hm3 : MBarGT D.M ⊥ V 3 := (c.hyp125.mBarGT_iff_lt_mBar 3).2 (by omega)
    have hP := c.hyp125.pairFacts
    have hVV : InCalV D.M V := ⟨hP.ne_bot, hP.le_M, hP.le_normalizer, hP.elemAbelian⟩
    have hV1 : InCalV1 D.M D.T V := by
      rcases c.hyp125.1 with h1 | h2
      · exact h1.1.1.1
      · have hnotTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V := by
          rcases h2.1 with ⟨-, -, -, -, hnotTI, -, -⟩
          exact hnotTI
        exact uc22p22n_inCalV1_of_not_isTI D hx h61 hVV hnotTI
    have hm2 : MBarGT D.M ⊥ V 2 := TwelveShort.mBarGT_mono hm3 (by omega)
    have hsp := TwelveShort.lt_sParam_of_mBarGT D h111 hV1 hm2 hm3
    have hsp4 : 4 ≤ E3.sParam hV1.1.2.2.2 := Nat.succ_le_of_lt hsp
    have hr4 : (4 : ℕ∞) ≤ rMV D.M V := by
      rw [rMV_eq_rParam_of_inCalV D hV1.1]
      exact (by exact_mod_cast hsp4 : (4 : ℕ∞) ≤ (E3.sParam hV1.1.2.2.2 : ℕ∞)).trans
        (E3.coe_sParam_le_rParam hV1.1.2.2.2)
    change (4 + mSub (⊥ : Subgroup G) : ℕ∞) ≤ rMV D.M V
    have hm0 : mSub (⊥ : Subgroup G) = 0 := by rw [mSub, rk_bot]
    rw [hm0]
    have hz : ((0 : ℕ) : ℕ∞) = 0 := by norm_num
    rw [hz, add_zero]
    exact hr4
  · exact seventeen_twentysix_b_three_of_ne D V₀ V hV h17_25 hx h61 h127 h1114 h162 hV0 L c

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
