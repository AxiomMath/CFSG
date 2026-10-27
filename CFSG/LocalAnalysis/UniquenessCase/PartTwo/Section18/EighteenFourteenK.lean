module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.Quasithin.Background.HPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_Table13_8_Omega6Minus_pi : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (p n s : ℕ),
    IsOmegaMinus ↥H 6 n → 1 ≤ s → s ≤ 2 →
      SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 n) H ⊤ ⊥ s → p.Prime →
        (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] →
          ∀ v : W, v ≠ 1 → p ∈ piSet (Opp p (centVec H v))

@[expose] def K_Omega6Minus_natIsoMod : Prop :=
  ∀ {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) (U₁ U₂ : Subgroup W) (n : ℕ),
    NatOmegaMinus H U₁ ⊥ 6 n → NatOmegaMinus H U₂ ⊥ 6 n →
      CFSG.Quasithin.H.Pair.IsoMod H U₁ U₂

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
