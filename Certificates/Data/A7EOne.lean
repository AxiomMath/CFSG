module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Perm

public section

open Equiv

namespace CFSG.Quasithin.H13.A7EOne

@[expose] def inH1 (σ : Perm (Fin 7)) : Prop :=
  ∀ x : Fin 7, (x : ℕ) < 4 ↔ ((σ x : Fin 7) : ℕ) < 4

instance (σ : Perm (Fin 7)) : Decidable (inH1 σ) := by unfold inH1; infer_instance

@[expose] def pInv : Perm (Fin 7) := swap 0 1 * swap 2 3 * swap 4 5

@[expose] def inH2 (σ : Perm (Fin 7)) : Prop := σ * pInv = pInv * σ

instance (σ : Perm (Fin 7)) : Decidable (inH2 σ) := by unfold inH2; infer_instance

@[expose] def stmt : Prop :=
  (Finset.univ.filter inH1).card = 144 ∧ (Finset.univ.filter inH2).card = 48 ∧
    (Finset.univ.filter fun σ => inH1 σ ∧ inH2 σ).card = 16 ∧
    (Finset.univ.filter fun σ => inH1 σ ∧ inH2 σ ∧ Perm.sign σ = 1).card = 8

instance : Decidable stmt := by unfold stmt; infer_instance

@[expose] def a7EOneCheck : Bool := decide stmt

end CFSG.Quasithin.H13.A7EOne
