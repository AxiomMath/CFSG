module

public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG

namespace FiveTransitive.PointStabilizerFixedSet

open MulAction SubMulAction FixedSetNormalizerPerm

theorem mem_fixed_iff (G X : Type) [Group G] [MulAction G X]
    (x : X) (R : Subgroup (stabilizer G x)) (y : ofStabilizer G x) :
    y ∈ fixedPoints R (ofStabilizer G x) ↔
      y.val ∈ fixedPoints (R.map (stabilizer G x).subtype) X := by
  constructor
  · intro hy q
    obtain ⟨r,hr,he⟩ := q.property
    change q.val • y.val = y.val
    rw [←he]
    exact congrArg Subtype.val (hy ⟨r,hr⟩)
  · intro hy r
    apply Subtype.ext
    exact hy ⟨r.val.val, ⟨r.val,r.property,rfl⟩⟩

private def fixedEquiv (G X : Type) [Group G] [MulAction G X]
    (x : X) (R : Subgroup (stabilizer G x)) :
    fixedPoints R (ofStabilizer G x) ≃
      ↥(fixedPoints (R.map (stabilizer G x).subtype) X \ {x}) where
  toFun y := ⟨y.val.val, (mem_fixed_iff G X x R y.val).mp y.property, y.val.property⟩
  invFun y := ⟨⟨y.val, y.property.2⟩,
    (mem_fixed_iff G X x R ⟨y.val,y.property.2⟩).mpr y.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fixed_card (G X : Type) [Group G] [MulAction G X] [Finite X]
    (x : X) (R : Subgroup (stabilizer G x)) :
    Nat.card (fixedPoints R (ofStabilizer G x)) =
      Nat.card (fixedPoints (R.map (stabilizer G x).subtype) X) - 1 := by
  rw [Nat.card_congr (fixedEquiv G X x R), Nat.card_coe_set_eq,
    Nat.card_coe_set_eq, Set.ncard_sdiff, Set.ncard_singleton]
  intro y hy
  have hyx : y = x := Set.mem_singleton_iff.mp hy
  subst y
  intro q
  obtain ⟨r,hr,he⟩ := q.property
  change q.val • x = x
  rw [←he]
  exact r.property

theorem mem_normalizer_map (G X : Type) [Group G] [MulAction G X]
    (x : X) (R : Subgroup (stabilizer G x)) (g : stabilizer G x)
    (hg : g ∈ Subgroup.normalizer (R : Set (stabilizer G x))) :
    g.val ∈ Subgroup.normalizer (R.map (stabilizer G x).subtype : Set G) := by
  exact Subgroup.le_normalizer_map (stabilizer G x).subtype
    ⟨g,hg,rfl⟩

end FiveTransitive.PointStabilizerFixedSet

end CFSG
