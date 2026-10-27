module


public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.Timmesfeld.TransvectionActions

variable {ActingGroup : Type*} [Group ActingGroup] {Space : Type*}
  [AddCommGroup Space] [Module (ZMod 2) Space]

@[expose] def IsElementaryAbelian2 (ActingGroup : Type*) [Group ActingGroup] : Prop :=
  (∀ first second : ActingGroup, first * second = second * first) ∧
    ∀ element : ActingGroup, element ^ 2 = 1

@[expose] def fixedSpace (action : Representation (ZMod 2) ActingGroup Space)
    (actingSet : Set ActingGroup) : Submodule (ZMod 2) Space where
  carrier := {vector | ∀ element ∈ actingSet, action element vector = vector}
  add_mem' := by
    intro first second firstFixed secondFixed element elementMem
    rw [map_add, firstFixed element elementMem, secondFixed element elementMem]
  zero_mem' := by
    intro element _
    exact map_zero _
  smul_mem' := by
    intro scalar vector vectorFixed element elementMem
    rw [map_smul, vectorFixed element elementMem]

@[expose] def displacement (action : Representation (ZMod 2) ActingGroup Space)
    (element : ActingGroup) : Space →ₗ[ZMod 2] Space :=
  action element - LinearMap.id

@[expose] def CommonTransvectionCenter (action : Representation (ZMod 2) ActingGroup Space)
    (center : Space) : Prop :=
  center ≠ 0 ∧ ∀ element : ActingGroup, element ≠ 1 →
    LinearMap.range (displacement action element) = Submodule.span (ZMod 2) {center}

theorem mem_fixedSpace {action : Representation (ZMod 2) ActingGroup Space}
    {actingSet : Set ActingGroup} {vector : Space} :
    vector ∈ fixedSpace action actingSet ↔
      ∀ element ∈ actingSet, action element vector = vector := Iff.rfl

theorem displacement_apply (action : Representation (ZMod 2) ActingGroup Space)
    (element : ActingGroup) (vector : Space) :
    displacement action element vector = action element vector - vector := by
  simp [displacement]

end CFSG.Timmesfeld.TransvectionActions
