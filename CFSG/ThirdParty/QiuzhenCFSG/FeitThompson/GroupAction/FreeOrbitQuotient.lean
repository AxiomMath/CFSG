module

public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index

namespace CFSG
end CFSG
open CFSG

/-!
# Subgroup orbits of free actions

For a free group action, the subgroup-orbit quotient splits as the product of
the full orbit quotient and the subgroup coset space.
-/

noncomputable section

namespace MulAction

/-- For a free G-action on X, every full G-orbit splits into copies indexed by
the left cosets of H when restricted to a subgroup H. -/
public noncomputable def orbitRelQuotientSubgroupEquivProd
    {G X : Type*} [Group G] [MulAction G X] [IsCancelSMul G X]
    (H : Subgroup G) :
    orbitRel.Quotient H X ≃ orbitRel.Quotient G X × (G ⧸ H) :=
  (equivSubgroupOrbits X H).trans
    ((Equiv.sigmaCongrRight fun (omega : orbitRel.Quotient G X) =>
      letI : IsCancelSMul G (orbitRel.Quotient.orbit omega) := {
        left_cancel' g x y h :=
          Subtype.ext (IsCancelSMul.left_cancel g x.1 y.1 (congrArg Subtype.val h))
        right_cancel' g h x eq :=
          IsCancelSMul.right_cancel g h x.1 (congrArg Subtype.val eq) }
      equivSubgroupOrbitsQuotientGroup
        (x := (⟨omega.out,
          orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' omega)⟩ :
            orbitRel.Quotient.orbit omega)) H).trans
      (Equiv.sigmaEquivProd _ _))

/-- For a finite free G-action, the number of H-orbits is the index of H
times the number of G-orbits. -/
public theorem natCard_orbitRelQuotient_subgroup
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [IsCancelSMul G X]
    [Finite (orbitRel.Quotient G X)] (H : Subgroup G) :
    Nat.card (orbitRel.Quotient H X) =
      H.index * Nat.card (orbitRel.Quotient G X) := by
  calc
    Nat.card (orbitRel.Quotient H X) =
        Nat.card (orbitRel.Quotient G X × (G ⧸ H)) :=
      Nat.card_congr (orbitRelQuotientSubgroupEquivProd H)
    _ = Nat.card (orbitRel.Quotient G X) * Nat.card (G ⧸ H) :=
      Nat.card_prod _ _
    _ = H.index * Nat.card (orbitRel.Quotient G X) := by
      rw [H.index_eq_card, Nat.mul_comm]

end MulAction
