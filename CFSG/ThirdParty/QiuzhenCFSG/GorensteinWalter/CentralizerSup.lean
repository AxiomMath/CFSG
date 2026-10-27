module

public import Mathlib.GroupTheory.Commutator.Basic

namespace CFSG
end CFSG
open CFSG

/-! # Centralizers of subgroup joins -/

namespace CFSG.GorensteinWalter

universe u

/-- A subgroup centralizing each of two subgroups centralizes their join. -/
public theorem le_centralizer_sup_of_le_centralizers
    {G : Type u} [Group G] {K A B : Subgroup G}
    (hKA : K ≤ Subgroup.centralizer (A : Set G))
    (hKB : K ≤ Subgroup.centralizer (B : Set G)) :
    K ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  intro k hk x hx
  rcases hx with hxA | hxB
  · exact (Subgroup.mem_centralizer_iff.mp (hKA hk)) x hxA
  · exact (Subgroup.mem_centralizer_iff.mp (hKB hk)) x hxB

end CFSG.GorensteinWalter
