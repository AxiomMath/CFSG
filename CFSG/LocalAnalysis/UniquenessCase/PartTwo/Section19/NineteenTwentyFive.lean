module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def HasL2SzSection (n : ℕ) (X : Subgroup G) : Prop :=
  ∃ Y : Subgroup G, Y ≤ X ∧ ∃ (Z : Subgroup ↥Y) (_ : Z.Normal),
    IsL2 (↥Y ⧸ Z) n ∨ IsSz (↥Y ⧸ Z) n

@[expose] def Gap19_25_72 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (h : Ctx19_10 D V₀ V p L A t B r) : Prop :=
  ∀ A₁ : Subgroup G, A₁ ≤ A → Nat.card A₁ = r →
    1 < CFSG.Open.pRank p (D.M ⊓ centralizer (A₁ : Set G)) →
      HasL2SzSection (S17.nOf L) (centralizer (A₁ : Set G) ⊓ IOf D p L) →
        normalizer (A₁ : Set G) ≤ D.M

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
