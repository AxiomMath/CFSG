module

public import Certificates.Certificate587001
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.H13.NPLSound

open CFSG.Quasithin.H13.NPL

@[expose] def S0 : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure {g : Equiv.Perm (Fin 8) | g ∈ S0gens ()}

theorem S0_le_alt : S0 ≤ alternatingGroup (Fin 8) := by
  unfold S0
  rw [Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]
  simp only [S0gens, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']

theorem S0_card : Nat.card S0 = 64 :=
  Certificates.certificate587001.1

theorem big_of_ne_one (σ : Equiv.Perm (Fin 8))
    (h1 : σ ≠ 1) (h5 : σ ^ 5 = 1 ∨ σ ^ 7 = 1) :
    448 < Nat.card ↥(Subgroup.closure (insert σ (↑S0 : Set (Equiv.Perm (Fin 8))))) :=
  Certificates.certificate587001.2 σ h1 h5

end CFSG.Quasithin.H13.NPLSound

end
