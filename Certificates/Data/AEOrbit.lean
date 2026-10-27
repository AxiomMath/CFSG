module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Finset.Powerset

public section

namespace Certificates.AEOrbit

@[expose] def cands (m : ℕ) : List (Equiv.Perm (Fin m)) :=
  ((List.finRange m).flatMap fun a => (List.finRange m).flatMap fun b =>
      (List.finRange m).flatMap fun c =>
        if a < b ∧ a < c ∧ b ≠ c then [Equiv.swap a b * Equiv.swap b c] else []) ++
    ((List.finRange m).flatMap fun a => (List.finRange m).flatMap fun b =>
      (List.finRange m).flatMap fun c => (List.finRange m).flatMap fun d =>
        if a < b ∧ c < d ∧ a < c ∧ b ≠ c ∧ b ≠ d then [Equiv.swap a b * Equiv.swap c d] else [])

@[expose] def fours (m : ℕ) : Finset (Finset (Fin m)) := (Finset.univ : Finset (Fin m)).powersetCard 4

@[expose] def moves (m : ℕ) (δ : Finset (Fin m)) : List (Equiv.Perm (Fin m)) :=
  (cands m).filter fun σ => Equiv.Perm.sign σ = 1 ∧ δ.image σ = δ

@[expose] def step {m : ℕ} (L : List (Equiv.Perm (Fin m))) (S : Finset (Finset (Fin m))) :
    Finset (Finset (Fin m)) :=
  S ∪ S.biUnion fun γ => (L.map fun (σ : Equiv.Perm (Fin m)) => γ.image σ).toFinset

@[expose] def reach (m : ℕ) (α β : Finset (Fin m)) : ℕ → Finset (Finset (Fin m))
  | 0 => {α}
  | k + 1 => step (moves m α ++ moves m β) (reach m α β k)

@[expose] def check (_ : Unit := ()) : Bool :=
  decide (∀ α ∈ fours 5, ∀ β ∈ fours 5, α ≠ β → reach 5 α β 4 = fours 5) &&
    decide (∀ α ∈ fours 6, ∀ β ∈ fours 6, α ≠ β → reach 6 α β 4 = fours 6)

end Certificates.AEOrbit
