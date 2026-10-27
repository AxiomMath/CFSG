module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def S1611e3V1SixGap : Prop :=
  ∀ (W W' : Type) [CommGroup W] [Finite W] [CommGroup W'] [Finite W'],
    (∀ w : W, w ^ 2 = 1) →
    ∀ (M L : Subgroup (MulAut W)) (L' : Subgroup (MulAut W')) (κ : W →* W')
      (e : ↥L' →* ↥L), L ≤ M → Nonempty (↥M ≃* MulAut ↥(alternatingGroup (Fin 6))) →
      UC22.IsAlt ↥L 6 →
      SumOfTwoInequiv (fun H U Z => AlternatingNatural H U Z 6) L' ⊤ ⊥ →
      Function.Surjective κ → Function.Surjective e →
      (∀ (b : ↥L') (w : W), κ ((e b : MulAut W) w) = (b : MulAut W') (κ w)) →
      (∀ w : W, κ w = 1 → w ∈ fixV L) → commV L = ⊤ → fixV L' = ⊥ → κ.ker ≠ ⊥ →
      ∀ E ∈ E3.aSet 2 M, False

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
