module

public import CFSG.Quasithin.Background.E2TwoLieQuotDisj

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def LiePerfOvergroupFactRank2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ k : ℕ, 2 ≤ k ∧ (IsPSL 3 2 k S ∨ IsPSp4 2 k S ∨ IsG2 2 k S ∨ Is3D4 2 k S ∨ Is2F4 k S)) →
    ∀ P : Subgroup S, IsSylowTwoOf P ⊤ →
      ∀ X : Subgroup S, P ≤ X → X ≠ ⊤ →
        ∀ Y : Subgroup S, Y ≤ X → (Y.subgroupOf X).IsSubnormal → ⁅Y, Y⁆ = Y → Y ≠ ⊥ →
          ∃ (B : Type) (_ : Group B) (f : ↥Y →* B), Function.Surjective f ∧
            ∃ m : ℕ, E2.IsBenderOf m B

@[expose] def ExcRank2NotSmallFact : Prop :=
  ∀ (S : Type) [Group S], (∃ k : ℕ, 2 ≤ k ∧ (IsG2 2 k S ∨ Is3D4 2 k S ∨ Is2F4 k S)) →
    ¬ E2.IsE22SmallType S

end CFSG.Quasithin.H13
