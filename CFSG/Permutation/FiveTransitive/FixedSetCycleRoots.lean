module

public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm
public import CFSG.Permutation.FiveTransitive.CyclePatternRoots
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Actions

public section

namespace CFSG

namespace FiveTransitive.FixedSetCycleRoots

open MulAction Equiv FixedSetNormalizerPerm CyclePatternRoots

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def twoEmbedding (Q : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)) :
    TwoRoot (fixedPerm G X Q a ha) ↪ TwoRoot (toPermHom G X a) where
  toFun x := ⟨x.val.val, by
    constructor
    · have h := congrArg Subtype.val x.property.1
      exact h
    · intro h
      exact x.property.2 (Subtype.ext h)⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.val) h

@[expose] def fixedEmbedding (Q : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)) :
    Function.fixedPoints (fixedPerm G X Q a ha) ↪ Function.fixedPoints (toPermHom G X a) where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.val) h

@[expose] def liftTuple {I : Type*} (Q : Subgroup G) (e : I ↪ X)
    (he : ∀ i, e i ∈ fixedPoints Q X) : I ↪ fixedPoints Q X where
  toFun i := ⟨e i,he i⟩
  inj' := fun _ _ h => e.injective (congrArg Subtype.val h)

end FiveTransitive.FixedSetCycleRoots

end CFSG
