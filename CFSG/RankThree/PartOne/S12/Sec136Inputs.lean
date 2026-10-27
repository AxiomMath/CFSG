module

public import CFSG.RankThree.PartOne.S12.Facts13
public import CFSG.RankThree.PartOne.S12.KFTransfer
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def KF136Refl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A → RowModel p L 10 →
    ∀ y ∈ torusImage E (cNormalizer c), y * y = 1 →
      (∃ hc : c ∈ E, y ⟨c, hc⟩ = ⟨c, hc⟩⁻¹) →
      Nat.card ↥(autFixedInG E y ⊓ L) = p ^ 2 →
      ∃ t ∈ reflectionSet p E, t ∈ torusImage E L ∧ ∀ b : E, (b : G) ∈ L → y b = t b

@[expose] def KF136At : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A → 1 ≤ f → p ∣ 2 ^ f + 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 3 2 f →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → KFAt p E f t

end CFSG.RankThree.PartOne
