module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Small

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def K14_5SmallFor (S : ∀ (L : Type) [Group L], ℕ → Prop) : Prop :=
  ∀ (I : Type) [CommGroup I] [Finite I], (∀ w : I, w ^ 2 = 1) →
    ∀ (X L P : Subgroup (MulAut I)) (e n : ℕ),
      L ≤ X → (L.subgroupOf X).Normal → CFSG.Open.IsQuasisimple ↥L → IsIrrOn L ⊤ ⊥ →
      S ↥L e →
      P ≤ L → IsParabolicTwo ↥L (P.subgroupOf L) → Hinf P ≠ ⊥ → NParam (Hinf P) n → 2 < n →
      E3.mParam X ≤ n + 1 →
        (∃ k : ℕ, IsNaturalClassicalModule L k ∧ (n = k ∨ n = 2 * k)) ∨
          (IsL2 ↥L 3 ∧ n = 3 ∧ E3.mParam X = 4 ∧ E3.aParam X ≤ 1)

theorem K14_5SmallFor.or {S₁ S₂ : ∀ (L : Type) [Group L], ℕ → Prop} (h₁ : K14_5SmallFor S₁)
    (h₂ : K14_5SmallFor S₂) : K14_5SmallFor fun L _ e => S₁ L e ∨ S₂ L e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS
  rcases hS with hS | hS
  · exact h₁ I hI X L P e n hLX hLn hq hirr hS
  · exact h₂ I hI X L P e n hLX hLn hq hirr hS

theorem k14_5Small_of_rows
    (hL2 : K14_5SmallFor fun L _ e => IsL2 L e) (hSz : K14_5SmallFor fun L _ e => IsSz L e)
    (hU3 : K14_5SmallFor fun L _ e => IsU3 L e) (hSU3 : K14_5SmallFor fun L _ e => IsSU3 L e)
    (hL3 : K14_5SmallFor fun L _ e => IsL3 L e) (hSL3 : K14_5SmallFor fun L _ e => IsSL3 L e)
    (hSp4 : K14_5SmallFor fun L _ e => IsSp4 L e) (hU4 : K14_5SmallFor fun L _ e => IsU4 L e)
    (hG2 : K14_5SmallFor fun L _ e => IsG2 L e) (h3D4 : K14_5SmallFor fun L _ e => Is3D4 L e)
    (h2F4 : K14_5SmallFor fun L _ e => LieModel L .twistedF4 0 2 e)
    (hU5 : K14_5SmallFor fun L _ e => e = 2 ∧ IsU5 L 2)
    (hL4 : K14_5SmallFor fun L _ e => LieModel L .PSL 4 2 e)
    (hSp6 : K14_5SmallFor fun L _ e => LieModel L .PSp 3 2 e)
    (hO8 : K14_5SmallFor fun L _ e => IsOmega8m L e) : K14_5Small :=
  hL2.or <| hSz.or <| hU3.or <| hSU3.or <| hL3.or <| hSL3.or <| hSp4.or <| hU4.or <| hG2.or <|
    h3D4.or <| h2F4.or <| hU5.or <| hL4.or <| hSp6.or hO8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
