module

public import CFSG.Quasithin.Recognition.RuTypeDefs

public section

namespace CFSG.Quasithin.RuType

open scoped MatrixGroups

@[expose] def StUniqueStatement : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (ρ : Representation (ZMod 2) SL(3, ZMod 2) M),
    Nat.card M = 2 ^ 8 →
    (∀ N : Submodule (ZMod 2) M, (∀ g : SL(3, ZMod 2), ∀ m ∈ N, ρ g m ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∃ χ : M →+ Matrix (Fin 3) (Fin 3) (ZMod 2),
      Function.Injective χ ∧ (∀ m, IsTraceZero (χ m)) ∧
      (∀ A, IsTraceZero A → ∃ m, χ m = A) ∧
      ∀ (g : SL(3, ZMod 2)) (m : M), χ (ρ g m) = stAct g (χ m)

end CFSG.Quasithin.RuType
