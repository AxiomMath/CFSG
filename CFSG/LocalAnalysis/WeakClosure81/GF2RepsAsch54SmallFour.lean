module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxG2Pair
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem isSolvable_normalizer_of_card_le_four {Q : Type} [Group Q] [Finite Q] {E : Subgroup Q}
    [E.Normal] (hq : Group.IsSolvable (Q ⧸ E)) {V : Subgroup Q} (hV : Nat.card ↥V ≤ 4)
    (hC : Group.IsSolvable ↥(E.subgroupOf (Subgroup.centralizer (V : Set Q)))) :
    Group.IsSolvable ↥(Subgroup.normalizer (V : Set Q)) := by
  have := hC
  have := hq
  have : Group.IsSolvable ↥(Subgroup.centralizer (V : Set Q)) := by
    refine Group.isSolvable_of_ker_le_range
      (E.subgroupOf (Subgroup.centralizer (V : Set Q))).subtype
      ((QuotientGroup.mk' E).comp (Subgroup.centralizer (V : Set Q)).subtype) fun x hx => ?_
    rw [Subgroup.range_subtype, Subgroup.mem_subgroupOf]
    exact (QuotientGroup.eq_one_iff _).1 hx
  have : Group.IsSolvable (Equiv.Perm ↥V) := Equiv.Perm.isSolvable hV
  have : Group.IsSolvable (MulAut ↥V) :=
    Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm ↥V)
      fun a b h => MulEquiv.ext fun x => congrArg (fun p : Equiv.Perm ↥V => p x) h
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (Subgroup.centralizer_le_normalizer (V : Set Q))) V.normalizerMonoidHom ?_
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.inclusion_range]

theorem natCard_sup_zpowers_le_four {Q : Type} [Group Q] [Finite Q] {z u : Q} (hz : z * z = 1)
    (hu : u * u = 1) (hzu : z * u = u * z) :
    Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers u) ≤ 4 := by
  classical
  have hsub : ((Subgroup.zpowers z ⊔ Subgroup.zpowers u : Subgroup Q) : Set Q) ⊆
      (({1, z, u, z * u} : Finset Q) : Set Q) := fun x hx => by
    rcases Asch80G2.mem_sup_zpowers hz hu hzu hx with h | h | h | h <;> simp [h]
  calc Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers u)
      ≤ Nat.card ↥(({1, z, u, z * u} : Finset Q) : Set Q) := Nat.card_mono (Set.toFinite _) hsub
    _ = ({1, z, u, z * u} : Finset Q).card := by simp
    _ ≤ 4 := Finset.card_le_four

end CFSG.LocalAnalysis.WeakClosure81

end
