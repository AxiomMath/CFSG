module

public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import Mathlib.Combinatorics.SimpleGraph.Init

public section

universe u v w

namespace CFSG.AlternatingAutomorphism

open Equiv Equiv.Perm Finset in
theorem _root_.CFSG.Milestones.alternating_automorphism_permutation {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (f : MulAut (alternatingGroup (Fin n))) :
    ∃ σ : Perm (Fin n), ∀ g : alternatingGroup (Fin n),
      (f g : Perm (Fin n)) = σ * (g : Perm (Fin n)) * σ⁻¹ :=
  _root_.CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le hn f

end CFSG.AlternatingAutomorphism
