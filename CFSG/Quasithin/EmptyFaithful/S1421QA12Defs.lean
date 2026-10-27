module

public import CFSG.Quasithin.EmptyFaithful.S1421L11

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace QA12

@[expose] def IsRankTwoLie (n : ℕ) (X : Type) [Group X] : Prop :=
  IsPSL 3 2 n X ∨ IsSL3 (2 ^ n) X ∨ IsPSp4 2 n X

@[expose] def IsTwoParabolicsOver {X : Type} [Group X] (U P P' : Subgroup X) : Prop :=
  P ≠ P' ∧ U ≤ P ∧ U ≤ P' ∧ Subgroup.normalizer (U : Set X) ≤ P ⊓ P' ∧
    ∀ A : Subgroup X, U ≤ A → (A ⋖ (⊤ : Subgroup X) ↔ A = P ∨ A = P')

@[expose] def LieSylowLePerfectCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → IsRankTwoLie n X →
    ∀ U P P' : Subgroup X, IsSylowTwoOf U ⊤ → IsTwoParabolicsOver U P P' →
      U ≤ perfectCore P ∧ U ≤ perfectCore P'

@[expose] def LieTorusCoincide : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → IsRankTwoLie n X →
    ∀ U P P' B : Subgroup X, IsSylowTwoOf U ⊤ → IsTwoParabolicsOver U P P' →
      S1421.IsHallOdd B (Subgroup.normalizer (U : Set X)) →
      B ⊓ perfectCore P = B ⊓ perfectCore P' →
        IsPSL 3 2 2 X ∧ B ≤ perfectCore P ⊓ perfectCore P' ∧ Nat.card B = 3

end QA12

end CFSG.Quasithin
