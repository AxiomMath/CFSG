module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (eGenP)
open CFSG.SignalizerFunctorTheorem.McBride.Near (IsChiefFactorOf)
open scoped Pointwise

@[expose] def W3Lem45_2Chief : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (T : Subgroup Q) (j : ℕ) (Ω : Set (Subgroup Q))
    (F Z : Subgroup Q),
    1 ≤ j → IsSylowIn 2 T ⊤ → IsInvColl ⊤ Ω → Ω.Nonempty → (∀ A ∈ Ω, A ≠ ⊥) →
    CompFactorAutInF j ⊤ T → pCoreOf 2 (⊤ : Subgroup Q) = ⊥ →
    ⁅F, F⁆ = F → Z ≤ Subgroup.centralizer (F : Set Q) → IsChiefFactorOf ⊤ F Z →
    Subgroup.centralizer (F : Set Q) ≤ F → F ⊔ T = ⊤ →
      F = Z ⊔ ((eGenP j ⊤ T Ω ⊔ T) ⊓ F) ∨
        F = Z ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set Q) ⊓ F)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
