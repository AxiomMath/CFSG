module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK

structure BarConf (X : Type) [Group X] (B P : Subgroup X) : Prop extends BarSituation X B where
  isPGroup : IsPGroup 2 P
  index_odd : ¬ 2 ∣ P.index
  le : B ≤ P
  normalizer_le : ∀ d ∈ Subgroup.normalizer (P : Set X), d ∈ Subgroup.normalizer (B : Set X)
  free : ∀ x : X, (∃ a ∈ B, ∃ b ∈ CFSG.Quasithin.conjSubgroup B x, a * b ≠ b * a) →
    ∀ a ∈ B, a ∈ Subgroup.normalizer ((CFSG.Quasithin.conjSubgroup B x : Subgroup X) : Set X) →
      a = 1

@[expose] def NoHyp85 (X : Type) [Group X] (B : Subgroup X) : Prop :=
  (¬ ∃ m n : ℕ, 3 < m ∧ IsSpGp (X ⧸ Subgroup.center X) m n ∧ Nat.card B = 2 ^ n) ∧
    (¬ ∃ m n : ℕ, 3 < m ∧ IsPSUGp (X ⧸ Subgroup.center X) m n ∧ Nat.card B = 2 ^ n) ∧
    (¬ ∃ k : ℕ, 3 < k ∧ IsSymGp (X ⧸ fusionOddCore X) k)

@[expose] def HatShape166 (X : Type) [Group X] (B : Subgroup X) (n : ℕ) : Prop :=
  Nat.card B = 2 ^ n ∧
    ((1 < n ∧ (IsSpGp (X ⧸ Subgroup.center X) 2 n ∨ IsSzGp (X ⧸ Subgroup.center X) n ∨
        IsPSUGp (X ⧸ Subgroup.center X) 3 n)) ∨
      (n = 1 ∧ B ⊔ fusionOddCore X = ⊤))

end CFSG.LocalAnalysis.WeakClosure81

end
