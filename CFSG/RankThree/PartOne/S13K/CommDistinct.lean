module

public import CFSG.RankThree.PartOne.S13K.KFLift
public import CFSG.RankThree.PartOne.S13K.HasTwoSub

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory

@[expose] def KFCommDistinct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, KFLiftAt p E s → KFLiftAt p E t →
    (E ≠ A ∨ HasTwoSub E (kZero p E s) ∨ HasTwoSub E (kZero p E t)) →
    s * t = t * s → ∀ e ∈ autFixedInG E s ⊓ autFixedInG E t, e ≠ 1 →
    ∀ I₁ ∈ thetaComponentsAt p e, ∀ I₂ ∈ thetaComponentsAt p e, I₁ ≠ I₂ →
      kZero p E s ≤ I₁ → kZero p E t ≤ I₂ →
      kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G)

end CFSG.RankThree.PartOne.S13K
