module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Inputs
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def A23FourCentralFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    A23List S → ∀ P E : Subgroup S, IsSylowTwoOf P ⊤ → E ≤ P → IsElemAbelian 2 E →
      Nat.card E = 16 → P ≤ Subgroup.normalizer (E : Set S) →
      (P ⊓ Subgroup.centralizer (E : Set S)).relIndex P ≤ 2 →
        IsLieChar2Big S ∧ E ≤ Subgroup.centralizer (P : Set S)

@[expose] def LieMultiplierFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X → ∀ (Z : Subgroup X) [Z.Normal],
    Z ≤ Subgroup.center X → IsPGroup 2 Z → IsLieChar2Big (X ⧸ Z) →
    ∀ P E : Subgroup (X ⧸ Z), IsSylowTwoOf P ⊤ → E ≤ P → IsElemAbelian 2 E →
      Nat.card E = 16 → E ≤ Subgroup.centralizer (P : Set (X ⧸ Z)) → Z = ⊥

@[expose] def LieCartanFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsLieChar2Big S →
    ∀ P Y E : Subgroup S, IsSylowTwoOf P ⊤ → Y ≤ Subgroup.normalizer (P : Set S) →
      Odd (Nat.card Y) → Nat.card Y * Nat.card P = Nat.card (Subgroup.normalizer (P : Set S)) →
      E ≤ P → IsElemAbelian 2 E → Nat.card E = 16 → E ≤ Subgroup.centralizer (P : Set S) →
        (∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) ∧
        3 < (Y ⊓ Subgroup.centralizer (E : Set S)).relIndex Y ∧
        (Y ⊓ Subgroup.centralizer (E : Set S) = ⊥ →
          ∃ k : ℕ, 2 ≤ k ∧ (IsPSL 2 2 k S ∨ IsSz k S ∨ IsPSp4 2 k S))

@[expose] def LieThompsonFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K K' Q : Subgroup G),
    IsSimpleGroup ↥K → (∃ k : ℕ, 2 ≤ k ∧ (IsPSL 2 2 k ↥K ∨ IsSz k ↥K ∨ IsPSp4 2 k ↥K)) →
    IsPGroup 2 ↥Q → (K' = K ∨ ∃ r ∈ Q, K' = CFSG.conjugate K r ∧ ⁅K, K'⁆ = ⊥) →
    Q ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) → IsSylowTwoOf (Q ⊓ K) K →
    (∃ E : Subgroup G, E ≤ Q ⊓ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
      E ≤ Subgroup.centralizer ((Q ⊓ K : Subgroup G) : Set G)) →
    ∀ A : Subgroup G, IsMaxElemAbelian Q A →
      A ≤ ((Q ⊓ K) ⊔ (Q ⊓ K')) ⊔ (Q ⊓ Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G))

end CFSG.Quasithin.H13
