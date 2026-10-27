module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def Shape14_5 (L : Type) [Group L] (e : ℕ) : Prop :=
  IsL2 L e ∨ IsSz L e ∨ IsU3 L e ∨ IsSU3 L e ∨ IsL3 L e ∨ IsSL3 L e ∨ IsSp4 L e ∨ IsU4 L e ∨
    IsG2 L e ∨ Is3D4 L e ∨ LieModel L .twistedF4 0 2 e ∨ (e = 2 ∧ IsU5 L 2) ∨
    LieModel L .PSL 4 2 e ∨ LieModel L .PSp 3 2 e ∨ IsOmega8m L e

@[expose] def K14_5Small : Prop :=
  ∀ (I : Type) [CommGroup I] [Finite I], (∀ w : I, w ^ 2 = 1) →
    ∀ (X L P : Subgroup (MulAut I)) (e n : ℕ),
      L ≤ X → (L.subgroupOf X).Normal → CFSG.Open.IsQuasisimple ↥L → IsIrrOn L ⊤ ⊥ →
      Shape14_5 ↥L e →
      P ≤ L → IsParabolicTwo ↥L (P.subgroupOf L) → Hinf P ≠ ⊥ → NParam (Hinf P) n → 2 < n →
      E3.mParam X ≤ n + 1 →
        (∃ k : ℕ, IsNaturalClassicalModule L k ∧ (n = k ∨ n = 2 * k)) ∨
          (IsL2 ↥L 3 ∧ n = 3 ∧ E3.mParam X = 4 ∧ E3.aParam X ≤ 1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
