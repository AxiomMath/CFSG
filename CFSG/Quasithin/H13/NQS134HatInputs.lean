module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.H13.NQS134

@[expose] def HatA6OddInverts : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X → Nat.card ↥(Subgroup.center X) = 3 →
    ∀ (e : X ⧸ Subgroup.center X ≃* ↥(alternatingGroup (Fin 6))) (α : MulAut X)
      (σ : Equiv.Perm (Fin 6)), Equiv.Perm.sign σ = -1 →
      (∀ x : X, ((e (α x : X ⧸ Subgroup.center X) : Equiv.Perm (Fin 6))) =
        σ * (e (x : X ⧸ Subgroup.center X) : Equiv.Perm (Fin 6)) * σ⁻¹) →
      ∀ z ∈ Subgroup.center X, α z = z⁻¹

end CFSG.Quasithin.H13.NQS134
