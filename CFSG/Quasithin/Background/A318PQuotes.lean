module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def QSporOutTwo : Prop :=
  ¬ 3 ∣ Nat.card (Outer (NativeSporadic.Carrier .J4))

@[expose] def LieTwoFamily (S : Type) [Group S] : Prop :=
  (∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel S .PSU 3 2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
  (∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
  (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f)

@[expose] def QLiePRank : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X) [S.Normal],
    (∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) → IsSimpleGroup ↥S → LieTwoFamily ↥S →
    1 < CFSG.Open.pRank p S → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 →
    ∀ x : X, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ S

@[expose] def QLieThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X) [S.Normal],
    (∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) → IsSimpleGroup ↥S →
    (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel ↥S .twistedF4 2 f) →
    1 < CFSG.Open.pRank 3 S → CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 →
    ∀ x : X, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ S

end CFSG.Quasithin
