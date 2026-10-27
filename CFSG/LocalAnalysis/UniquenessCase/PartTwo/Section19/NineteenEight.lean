module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem nineteen_seven_gt_three (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h197 : R19_7At D V₀ V p L K h) :
    3 < mBar D.M V₀ V h.hyp.isElemAbelian :=
  (Hyp125.mBarGT_iff_lt_mBar h.hyp.hyp125 3).1 h197

theorem nineteen_eight_one_r (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h197 : R19_7At D V₀ V p L K h) :
    ((mSub V₀ + mBar D.M V₀ V h.hyp.isElemAbelian : ℕ) : ℕ∞) ≤ rMV D.M V := by
  have hV₀ : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hW : WeakClosureSetting D V₀ V :=
    weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h.hyp.hyp125 hV₀
  have hm1 : 1 < mBar D.M V₀ V h.hyp.isElemAbelian :=
    lt_trans (by norm_num) (nineteen_seven_gt_three D h h197)
  have h2 := h162 D V₀ V hW hx h61 hV₀ hm1
  simpa [Nat.add_comm] using h2

theorem nineteen_eight_three_upper (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h194 : R19_4At D V₀ V p L K h) : 2 + mSub V₀ ≤ 6 := by
  have h4 : mSub V₀ ≤ 4 := h194
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
