module

public import CFSG.RankThree.PartOne.S12.KFTransfer
public import CFSG.RankThree.PartOne.S12.Facts13

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def Row7Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → 1 ≤ f → p ∣ 2 ^ f - 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f →
    (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → KFAt p E f s) ∧ Subgroup.center L = ⊥ ∧
      ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ s' ∈ reflectionSet p E,
        s' ∈ torusImage E L → orderOf (s * s') = 4 → kZero p E s ⊔ kZero p E s' = L

@[expose] def Row5Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → 1 ≤ f → p ∣ 2 ^ f - 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f →
    Subgroup.center L = ⊥ ∧
      ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ s' ∈ reflectionSet p E,
        s' ∈ torusImage E L → orderOf (s * s') = 4 →
        ((KFAt p E f s ∧ KFAt p E (2 * f) s') ∨ (KFAt p E (2 * f) s ∧ KFAt p E f s')) ∧
          kZero p E s ⊔ kZero p E s' = L

end CFSG.RankThree.PartOne.K1320
