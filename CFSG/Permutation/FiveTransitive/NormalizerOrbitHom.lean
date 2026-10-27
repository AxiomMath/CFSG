module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitPermutation
public import Mathlib.Algebra.Group.Action.End

public section

namespace CFSG

namespace FiveTransitive.NormalizerOrbitHom

open MulAction

@[expose] def toPermHom {G Y : Type*} [Group G] [MulAction G Y] (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) →* Equiv.Perm (orbitRel.Quotient Q Y) where
  toFun := NormalizerOrbitPermutation.orbitPerm Q
  map_one' := by
    apply Equiv.ext
    intro O
    induction O using Quotient.inductionOn with
    | h y =>
      change Quotient.mk'' ((1 : G) • y) = Quotient.mk'' y
      rw [one_smul]
  map_mul' x z := by
    apply Equiv.ext
    intro O
    induction O using Quotient.inductionOn with
    | h y =>
      change Quotient.mk'' ((x.val * z.val) • y) = Quotient.mk'' (x.val • (z.val • y))
      rw [mul_smul]

theorem apply_subgroup_eq_one {G Y : Type*} [Group G] [MulAction G Y]
    (Q : Subgroup G) (q : Q) :
    toPermHom (Y := Y) Q ⟨q.val, Q.le_normalizer q.property⟩ = 1 := by
  apply Equiv.ext
  intro O
  induction O using Quotient.inductionOn with
  | h y =>
    change Quotient.mk'' (q • y) = (Quotient.mk'' y : orbitRel.Quotient Q Y)
    exact orbitRel.Quotient.quotient_smul_eq

theorem inside_le_ker {G Y : Type*} [Group G] [MulAction G Y] (Q : Subgroup G) :
    Q.subgroupOf (Subgroup.normalizer (Q : Set G)) ≤ (toPermHom (Y := Y) Q).ker := by
  intro q hq
  exact apply_subgroup_eq_one Q ⟨q.val, hq⟩

@[expose] abbrev action {G Y : Type*} [Group G] [MulAction G Y] (Q : Subgroup G) :
    MulAction (Subgroup.normalizer (Q : Set G)) (orbitRel.Quotient Q Y) :=
  MulAction.compHom _ (toPermHom (Y := Y) Q)

@[expose] def liftNormal {G : Type*} [Group G] (Q : Subgroup G) [Q.Normal] :
    G →* Subgroup.normalizer (Q : Set G) where
  toFun x := ⟨x, by rw [Subgroup.normalizer_eq_top Q]; trivial⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] abbrev normalAction {G Y : Type*} [Group G] [MulAction G Y]
    (Q : Subgroup G) [Q.Normal] : MulAction G (orbitRel.Quotient Q Y) :=
  MulAction.compHom _ ((toPermHom (Y := Y) Q).comp (liftNormal Q))

end FiveTransitive.NormalizerOrbitHom

end CFSG
