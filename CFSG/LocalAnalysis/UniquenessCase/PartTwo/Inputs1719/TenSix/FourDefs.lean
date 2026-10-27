module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

@[expose] def W4Lem10_5Four : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (p e q : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L →
      p.Prime → p ≠ 2 → 0 < e → q = p ^ e →
      InGq (↥L ⧸ Subgroup.center ↥L) q →
        4 ≤ E3.mParam Y ∨
        (LieModel ↥L .PSU 3 3 1 ∨ LieModel ↥L .PSp 2 3 1 ∨
          LieModel ↥L .PSL 2 2 3 ∨
          (LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1 ∧
            Subgroup.center ↥L ≠ ⊥)) ∨
        (LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 5 1 ∨
          LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 7 1 ∨
          LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 3 2)

@[expose] def W4Lem10_5ResidualThree : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (t : CFSG.Open.StatedLieTag) (n : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L →
      LieModel (↥L ⧸ Subgroup.center ↥L) t n 3 1 →
      ¬ (t = .PSU ∧ n = 3) → ¬ (t = .PSp ∧ n = 2) →
      ¬ (t = .PSU ∧ n = 4 ∧ Subgroup.center ↥L ≠ ⊥) →
        4 ≤ E3.mParam Y

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
