module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c2Gt2
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

@[expose] def W3Thm162Ext (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (D : Data G) (V₀ V : Subgroup G) (h : WeakClosureSetting D V₀ V), DataExt D → UC6.R6_1 D →
    V₀ ≠ ⊥ → 1 < mBar D.M V₀ V h.isElemAbelian →
      ((mBar D.M V₀ V h.isElemAbelian + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V

@[expose] def W3Thm162MuTwo (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (D : Data G) (V₀ V : Subgroup G) (h : WeakClosureSetting D V₀ V), DataExt D → UC6.R6_1 D →
    V₀ ≠ ⊥ → mBar D.M V₀ V h.isElemAbelian = 2 →
      ((mBar D.M V₀ V h.isElemAbelian + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V

theorem W3Thm162Ext.of_gt2 (h : W3Thm162Gt2 G) (h2 : W3Thm162MuTwo G) : W3Thm162Ext G := by
  intro D V₀ V hW hx h61 hV₀ hm
  by_cases h3 : 2 < mBar D.M V₀ V hW.isElemAbelian
  · exact h D V₀ V hW hV₀ h3
  · exact h2 D V₀ V hW hx h61 hV₀ (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
