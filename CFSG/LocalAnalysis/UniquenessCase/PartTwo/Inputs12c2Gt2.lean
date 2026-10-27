module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsSetting
public import CFSG.LocalAnalysis.WeakClosure81.SixSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

@[expose] def W3Thm162Gt2 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (D : Data G) (V₀ V : Subgroup G) (h : WeakClosureSetting D V₀ V), V₀ ≠ ⊥ →
    2 < mBar D.M V₀ V h.isElemAbelian →
      ((mBar D.M V₀ V h.isElemAbelian + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
