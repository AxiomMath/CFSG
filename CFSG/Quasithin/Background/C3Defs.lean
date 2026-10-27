
module

public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Groups

@[expose] def IsRankTwoLie2Over (n : ℕ) (X : Type) [Group X] : Prop :=
  IsPSL 3 2 n X ∨ IsPSp4 2 n X ∨ IsG2 2 n X ∨ Is3D4 2 n X ∨ Is2F4 n X ∨
    IsPSU 4 2 n X ∨ IsPSU 5 2 n X ∨
    (n = 1 ∧ (IsAlt 6 X ∨ IsPSU 3 3 1 X ∨ IsTits X))

theorem IsRankTwoLie2Over.isRankTwoLie2Derived {n : ℕ} {X : Type} [Group X]
    (h : IsRankTwoLie2Over n X) : IsRankTwoLie2Derived X := by
  unfold IsRankTwoLie2Over at h
  unfold IsRankTwoLie2Derived
  rcases h with h | h | h | h | h | h | h | ⟨-, h | h | h⟩
  · exact Or.inl ⟨n, h⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h⟩))))))))
  · exact Or.inr (Or.inl ⟨n, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))

@[expose] def IsSpecial2Group (a b : ℕ) (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 2 ^ a ∧ commutator X = Subgroup.center X ∧
    IsE2 b (X ⧸ Subgroup.center X)

@[expose] def IsDoubleCover (X S : Type) [Group X] [Group S] : Prop :=
  CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) = 2 ∧
    Nonempty (X ⧸ Subgroup.center X ≃* S)

variable {G : Type} [Group G]

@[expose] def imageModCenter (K X : Subgroup G) : Subgroup (↥K ⧸ Subgroup.center ↥K) :=
  (X.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))

end Groups

section Modules

variable {G : Type} [Group G]

@[expose] def IsNaturalSection (A V Z : Subgroup G) (N : Subgroup ↥A) {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] (Γ : Subgroup (Matrix.GeneralLinearGroup ι F)) : Prop :=
  A ≤ Subgroup.normalizer (V : Set G) ∧
    ∃ α : ↥A →* ↥Γ, Function.Surjective α ∧ α.ker = N ∧
      ∃ β : ↥V →* Multiplicative (ι → F), Function.Surjective β ∧ β.ker = Z.subgroupOf V ∧
        ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
          Multiplicative.toAdd (β v) =
            ((α a : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec
              (Multiplicative.toAdd (β u))

@[expose] def IsIndecomposableUnder (A V : Subgroup G) : Prop :=
  V ≠ ⊥ ∧ ∀ V₁ V₂ : Subgroup G, V₁ ≤ V → V₂ ≤ V → A ≤ Subgroup.normalizer (V₁ : Set G) →
    A ≤ Subgroup.normalizer (V₂ : Set G) → V₁ ⊓ V₂ = ⊥ → V₁ ⊔ V₂ = V → V₁ = ⊥ ∨ V₂ = ⊥

@[expose] def IsB48TwoModule (A V : Subgroup G) : Prop :=
  V ≤ A ∧ IsElemAbelian 2 V ∧ Nat.card V = 2 ^ 4 ∧ A ⊓ Subgroup.centralizer (V : Set G) = V ∧
    IsIndecomposableUnder A V ∧
    IsNaturalSection A V (V ⊓ Subgroup.centralizer (A : Set G)) (V.subgroupOf A)
      (StatedSL 3 (ZMod 2))

end Modules

end CFSG.Quasithin
