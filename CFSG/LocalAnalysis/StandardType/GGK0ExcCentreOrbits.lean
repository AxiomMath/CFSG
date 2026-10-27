module

public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.StandardType.GGK0ExcCentreU

@[expose] noncomputable def numOrbitsOn {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : ℕ :=
  Set.ncard {O : Set (Fin n) | ∃ i ∈ S, O = Set.range (fun k : ℤ => (σ ^ k) i)}

@[expose] noncomputable def orbitSize {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  Set.ncard (Set.range (fun k : ℤ => (σ ^ k) i))

end CFSG.StandardType.GGK0ExcCentreU

end
