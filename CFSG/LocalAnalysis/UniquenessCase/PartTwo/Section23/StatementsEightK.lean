module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

@[expose] def KWSp4 (W : ∀ (X : Type) [Group X], MulAut X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (a : ℕ), IsSp4 X a →
    ∀ θ : MulAut X, Odd (orderOf θ) → ¬ W X θ →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ r : ℕ, r.Prime → r ∣ 2 ^ a - 1 →
      ∃ P : Sylow r X, ∀ x ∈ (P : Subgroup X), θ x = x

@[expose] def KWU3 (W : ∀ (X : Type) [Group X], MulAut X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (a : ℕ), IsU3 X a →
    ∀ θ : MulAut X, Odd (orderOf θ) → ¬ W X θ →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ q : ℕ, q.Prime → 3 < q → q ∣ 2 ^ a + 1 →
      ∃ x : X, orderOf x = q ∧ θ x = x

@[expose] def KBor : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (a : ℕ), (IsL2 X a ∨ IsSz X a ∨ IsSp4 X a ∨ IsU3 X a) →
    ∀ (S : Sylow 2 X) (A : Subgroup X), IsMulCommutative A → Odd (Nat.card A) →
      Nat.card ↥((S : Subgroup X) ⊔ A) = Nat.card (S : Subgroup X) * Nat.card A →
      A ≤ Subgroup.normalizer ((S : Subgroup X) : Set X)

@[expose] def KCentL2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (a : ℕ), IsL2 X a →
    ∀ θ : MulAut X, Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
      ∃ s : ℕ, s ∣ a ∧ Odd (a / s) ∧ (∃ x : X, orderOf x = 2 ^ s - 1 ∧ θ x = x) ∧
        (s = 1 → ∃ x : X, orderOf x = 3 ∧ θ x = x)

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_8_Sz (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx23L D Ch, ∀ K : Subgroup G, K ∈ calC D.M → ∀ a : ℕ, IsSz (Bar2 K) a →
    (K.subgroupOf D.M).Normal

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
