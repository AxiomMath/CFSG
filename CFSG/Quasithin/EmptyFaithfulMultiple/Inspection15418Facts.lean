module

public import CFSG.Quasithin.Background.F6Cat

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def SylowCenterCyclic15418 : Prop :=
  ∀ (D : Type) [Group D] [Finite D],
    (F6.IsM12 D ∨ F6.IsAutM12 D ∨ ∃ p : ℕ, (p % 8 = 3 ∨ p % 8 = 5) ∧ F6.IsSLEps3GraphExt p D) →
    ∀ P : Sylow 2 D, IsCyclic ↥(Subgroup.center ↥(P : Subgroup D))

@[expose] def ComponentIndexTwo15418 : Prop :=
  ∀ (D : Type) [Group D] [Finite D],
    (F6.IsHatSym 6 D ∨ Nonempty (D ≃* Equiv.Perm (Fin 7)) ∨ F6.IsHatSym 7 D ∨
      ∃ p : ℕ, F6.IsL2FieldExtCat p D) →
    ∀ M : Subgroup D, CFSG.IsComponent M → M.index = 2

@[expose] def InvolutionCentralizer15418 : Prop :=
  ∀ (D : Type) [Group D] [Finite D],
    (Nonempty (D ≃* Equiv.Perm (Fin 7)) ∨ F6.IsHatSym 7 D ∨
      ∃ p : ℕ, 5 ≤ p ∧ F6.IsL2FieldExtCat p D) →
    ∀ M : Subgroup D, CFSG.IsComponent M → ∀ x ∈ M, x ^ 2 = 1 → x ≠ 1 →
      oddCoreIn (M ⊓ Subgroup.centralizer ({x} : Set D)) ≠ ⊥

end CFSG.Quasithin.EmptyFaithfulMultiple
