module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Perm

public section

open Equiv

namespace HatA7Loc

@[expose] def t0 : Perm (Fin 7) := swap 0 1 * swap 2 3

@[expose] def c : Perm (Fin 7) := swap 4 5 * swap 5 6

@[expose] def d : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 3 4 * swap 4 5

@[expose] def v2 : Perm (Fin 7) := swap 0 2 * swap 1 3

@[expose] def v3 : Perm (Fin 7) := swap 0 3 * swap 1 2

@[expose] def cent1 : Prop :=
  ∀ σ : Perm (Fin 7), σ * t0 = t0 * σ → σ ^ 315 = 1 → σ = 1 ∨ σ = c ∨ σ = c ^ 2

instance : Decidable cent1 := by unfold cent1; infer_instance

@[expose] def cent2 : Prop :=
  ∀ σ : Perm (Fin 7), Perm.sign σ = 1 → σ * c = c * σ → σ ^ 16 = 1 →
    σ = 1 ∨ σ = t0 ∨ σ = v2 ∨ σ = v3

instance : Decidable cent2 := by unfold cent2; infer_instance

@[expose] def cent3 : Prop :=
  ∀ σ : Perm (Fin 7), Perm.sign σ = 1 → σ * d = d * σ → σ ^ 16 = 1 → σ = 1

instance : Decidable cent3 := by unfold cent3; infer_instance

@[expose] def stmt : Prop := cent1 ∧ cent2 ∧ cent3

instance : Decidable stmt := by unfold stmt; infer_instance

@[expose] def check : Bool := decide stmt

end HatA7Loc
