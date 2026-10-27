module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.B4Models
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def W4Lem8_6 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (t : MulAut W) (n : ℕ),
      L ≤ Y → Fstar Y = L → IsAlt ↥L n → (n = 7 ∨ 9 ≤ n) → IsIrrOn L ⊤ ⊥ →
      t ∈ Y → orderOf t = 2 → E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3 →
      (n = 7 ∧ Nat.card W = 2 ^ 4 ∧ Y = L) ∨ AlternatingNatural L ⊤ ⊥ n

end CFSG.LocalAnalysis.WeakClosure81

end
