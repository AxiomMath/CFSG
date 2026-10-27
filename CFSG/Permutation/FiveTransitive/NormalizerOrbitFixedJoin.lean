module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitHom
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG

namespace FiveTransitive.NormalizerOrbitFixedJoin

open MulAction

private theorem fixedPoints_sup_zpowers
    {G Y : Type*} [Group G] [MulAction G Y]
    (Q : Subgroup G) (hQ : ∀ (q : Q) (y : Y), q • y = y) (x : G) :
    fixedPoints (Q ⊔ Subgroup.zpowers x : Subgroup G) Y = fixedBy Y x := by
  ext y
  rw [mem_fixedPoints]
  constructor
  · intro h
    exact h ⟨x, (le_sup_right : Subgroup.zpowers x ≤ Q ⊔ Subgroup.zpowers x) (Subgroup.mem_zpowers x)⟩
  · intro hx q
    have hle : Q ⊔ Subgroup.zpowers x ≤ stabilizer G y := by
      apply sup_le
      · intro r hr
        exact hQ ⟨r, hr⟩ y
      · exact Subgroup.zpowers_le.mpr hx
    exact hle q.property

theorem fixed_join_normal
    {G Y : Type*} [Group G] [MulAction G Y]
    (Q : Subgroup G) [Q.Normal] (x : G) :
    let _ := NormalizerOrbitHom.normalAction (Y := Y) Q
    fixedPoints (Q ⊔ Subgroup.zpowers x : Subgroup G) (orbitRel.Quotient Q Y) =
      Function.fixedPoints (NormalizerOrbitPermutation.orbitPerm (Y := Y) Q
        (NormalizerOrbitHom.liftNormal Q x)) := by
  let _ := NormalizerOrbitHom.normalAction (Y := Y) Q
  apply fixedPoints_sup_zpowers
  intro q y
  change NormalizerOrbitHom.toPermHom Q (NormalizerOrbitHom.liftNormal Q q.val) y = y
  have hq := NormalizerOrbitHom.apply_subgroup_eq_one (Y := Y) Q q
  change NormalizerOrbitHom.toPermHom Q (NormalizerOrbitHom.liftNormal Q q.val) = 1 at hq
  rw [hq]
  rfl

end FiveTransitive.NormalizerOrbitFixedJoin

end CFSG
