module

public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.KC.K1471PermTab

@[expose] def tab {n : ℕ} (p : Equiv.Perm (Fin n)) : List ℕ :=
  (List.range n).map fun i => if h : i < n then (p ⟨i, h⟩ : ℕ) else 0

end CFSG.KC.K1471PermTab

end
