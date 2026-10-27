module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open scoped Pointwise

@[expose] def KQ35NormSylow : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (n p : ℕ),
    (p = 3 ∨ p = 5) → StatedLieAdmissible t n p 1 → FunTwoType t n → LieModel X t n p 1 →
    ∀ (P : Sylow 2 X) (x : X), x ∈ normalizer ((P : Subgroup X) : Set X) →
      Odd (orderOf x) → orderOf x ∣ 3

@[expose] def KQ35NormSylowAlpha : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (n p : ℕ),
    (p = 3 ∨ p = 5) → StatedLieAdmissible t n p 1 → FunTwoType t n → LieModel X t n p 1 →
    ∀ (P : Sylow 2 X) (x : X), x ∈ normalizer ((P : Subgroup X) : Set X) →
      ∀ s m : ℕ, s.Prime → 7 ≤ s → Odd m → s ∣ 2 ^ m - 1 → orderOf x ≠ s

@[expose] def KQ35PermFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (n p : ℕ),
    ((t = .PSp ∧ n = 2 ∧ (p = 3 ∨ p = 5)) ∨ (t = .PSU ∧ n = 4 ∧ p = 3) ∨
      (t = .POmegaOdd ∧ n = 3 ∧ p = 3) ∨ (t = .G2 ∧ n = 0 ∧ p = 5)) →
    LieModel X t n p 1 → ∀ (P : Sylow 2 X) (R : Subgroup X), IsPGroup 5 R →
      (R : Set X) * (P : Set X) = (P : Set X) * (R : Set X) → R = ⊥

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
