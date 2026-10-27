module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Sylow

namespace CFSG
end CFSG
open CFSG

/-!
# Sylow subgroups inside finite cyclic subgroups

This module packages the ambient-subgroup form needed when taking the full
`p`-part of a cyclic torus.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A finite cyclic subgroup contains an ambient cyclic subgroup whose order
is the full `p`-part of the cyclic subgroup's order. -/
public theorem exists_cyclic_sylow_subgroup_le
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (U : Subgroup G) (hU : IsCyclic U) :
    ∃ R : Subgroup G,
      R ≤ U ∧ IsCyclic R ∧
        Nat.card R = p ^ (Nat.card U).factorization p := by
  let : IsCyclic U := hU
  let P : Sylow p U := Classical.choice Sylow.nonempty
  let R : Subgroup G := (P : Subgroup U).map U.subtype
  have hRU : R ≤ U := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.2
  have hRcyclic : IsCyclic R := by
    exact Subgroup.isCyclic_of_le hRU
  have hcard_map : Nat.card R = Nat.card P := by
    let e : P ≃* R :=
      (P : Subgroup U).equivMapOfInjective U.subtype U.subtype_injective
    exact Nat.card_congr e.toEquiv.symm
  refine ⟨R, hRU, hRcyclic, ?_⟩
  rw [hcard_map]
  exact Sylow.card_eq_multiplicity P

end CFSG.GorensteinWalter
