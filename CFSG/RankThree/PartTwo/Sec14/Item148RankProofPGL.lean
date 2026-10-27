module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank

@[expose] def KF148PGLPi : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (X E : Subgroup Γ),
    Group.IsPerfect ↥X → IsLThreePi ↥X →
    E ≤ Subgroup.normalizer (X : Set Γ) → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    (∀ g ∈ Subgroup.centralizer (E : Set Γ), g ^ 3 = 1 → g ∈ E) →
    (∃ z : Γ, z ≠ 1 ∧ E ⊓ Subgroup.centralizer (X : Set Γ) = Subgroup.zpowers z) →
    (∃ a ∈ E, ¬ InnerOn148 X a) →
    ∃ (p f : ℕ), 1 ≤ f ∧ IsZ3PGLThreeAt ↥(X ⊔ E) p f

end CFSG.RankThree.PartTwo.Sec14
