module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

@[expose] def W4Lem10_6Q : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (p e q : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L →
      p.Prime → p ≠ 2 → 0 < e → q = p ^ e → 3 < q →
      InGq (↥L ⧸ Subgroup.center ↥L) q →
        (9 < q → E3.aParam Y = 1) ∧ E3.aParam Y ≤ 2

@[expose] def W4Lem10_6ResidualQ : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (t : CFSG.Open.StatedLieTag) (n p e : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L →
      p.Prime → p ≠ 2 → 0 < e → ¬ (t = .PSL ∧ n = 2) →
      LieModel (↥L ⧸ Subgroup.center ↥L) t n p e → 3 < p ^ e →
        (9 < p ^ e → E3.aParam Y = 1) ∧ E3.aParam Y ≤ 2

@[expose] def W4Lem10_5Q : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (p e q : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L →
      p.Prime → p ≠ 2 → 0 < e → q = p ^ e → 3 < q →
      InGq (↥L ⧸ Subgroup.center ↥L) q →
        8 ≤ E3.mParam Y ∨
        (LieModel ↥L .PSL 3 3 1 ∧ 4 ≤ E3.mParam Y) ∨
        ((LieModel ↥L .PSL 4 3 1 ∨ LieModel ↥L .PSU 4 3 1 ∨
            LieModel ↥L .G2 0 3 1 ∨
            (∃ (Z : Subgroup ↥L) (hZ : Z.Normal), Z ≤ Subgroup.center ↥L ∧
              Nat.card Z = 3 ∧ LieModel (quotBy Z hZ) .G2 0 3 1) ∨
            LieModel ↥L .PSp 3 3 1) ∧
          6 ≤ E3.mParam Y) ∨
        (LieModel ↥L .PSU 3 3 1 ∨ LieModel ↥L .PSp 2 3 1 ∨
          LieModel ↥L .PSL 2 2 3 ∨
          (LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1 ∧
            Subgroup.center ↥L ≠ ⊥)) ∨
        ((LieModel ↥L .PSL 2 5 2 ∨ LieModel ↥L .PSL 2 p 1) ∧ 4 ≤ E3.mParam Y) ∨
        (LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 5 1 ∨
          LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 7 1 ∨
          LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 3 2)

@[expose] def W4Lem10_5ResidualQ : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (t : CFSG.Open.StatedLieTag) (n p e : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L →
      p.Prime → p ≠ 2 → 0 < e → ¬ (t = .PSL ∧ n = 2) →
      LieModel (↥L ⧸ Subgroup.center ↥L) t n p e → 3 < p ^ e →
        8 ≤ E3.mParam Y ∨
        (LieModel ↥L .PSL 3 3 1 ∧ 4 ≤ E3.mParam Y) ∨
        ((LieModel ↥L .PSL 4 3 1 ∨ LieModel ↥L .PSU 4 3 1 ∨
            LieModel ↥L .G2 0 3 1 ∨
            (∃ (Z : Subgroup ↥L) (hZ : Z.Normal), Z ≤ Subgroup.center ↥L ∧
              Nat.card Z = 3 ∧ LieModel (quotBy Z hZ) .G2 0 3 1) ∨
            LieModel ↥L .PSp 3 3 1) ∧
          6 ≤ E3.mParam Y) ∨
        (LieModel ↥L .PSU 3 3 1 ∨ LieModel ↥L .PSp 2 3 1 ∨
          LieModel ↥L .PSL 2 2 3 ∨
          (LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1 ∧
            Subgroup.center ↥L ≠ ⊥)) ∨
        ((LieModel ↥L .PSL 2 5 2 ∨ LieModel ↥L .PSL 2 p 1) ∧ 4 ≤ E3.mParam Y) ∨
        (LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 5 1 ∨
          LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 7 1 ∨
          LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 3 2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
