module

public import CFSG.RankThree.PartOne.S13K.KF132At

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory

@[expose] def KF132AtEx (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → r ≠ 4 → RowModel p L r → (r ≤ 8 → E = A) →
    (9 ≤ r → Nat.card E = p ^ 4) →
    ∃ t ∈ reflectionSet p E, t ∈ torusImage E L ∧
      ∃ f g : ℕ, RowModelF p L r f ∧ KRowDeg r f g ∧ KFAt p E g t

end CFSG.RankThree.PartOne.S13K
