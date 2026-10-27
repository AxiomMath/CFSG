module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def R95Two (D : Data G) : Prop :=
  ∀ Y H D₃ : Subgroup G, Hyp91 D Y H D₃ → H ≠ ⊤ →
    LieModel (BarO3 (Opp 3 Y)) .PSL 3 2 1 →
      (∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ S ≤ D.M) ∧
      ((∃ e : ℕ, 1 ≤ e ∧ LieModel (Lbar9 Y H) .PSL 2 7 e ∧ H = (H ⊓ D.M) ⊔ I9 H) ∨
        (∃ e : ℕ, 1 ≤ e ∧ LieModel (Lbar9 Y H) .PSU 3 7 e ∧
          IsSL2Cover ↥(Opp 3 (img9 H (H ⊓ D.M) ⊓ img9 H (L9 Y H))) 7 e))

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
