module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open Subgroup

@[expose] def K67CentL3U3 : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (p f : ℕ),
    ((p ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel J .PSL 3 p f) ∨
      (p ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel J .PSU 3 p f)) →
    ∀ x : J, orderOf x = 3 →
      IsCyclic (centralizer ({x} : Set J)) ∧ Nat.card (centralizer ({x} : Set J)) = (p ^ f) ^ 2 - 1

@[expose] def K67OuterInvL3U3 : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (p f : ℕ),
    ((p ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel J .PSL 3 p f) ∨
      (p ≠ 2 ∧ p ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel J .PSU 3 p f)) →
    ∀ α : MulAut J, α ^ 2 = 1 → α ∉ (MulAut.conj : J →* MulAut J).range →
      ∀ y : J, α y = y → orderOf y ≤ p ^ f + 1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
