module

public import CFSG.Milestones.ASVolI.B4Natural

public section

namespace CFSG.ASVolI

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin.JonesParshall Module

section Actions

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def burnsideB49x_muN : (W ≃ₗ[ZMod 2] W) →* AddMonoid.End (W →ₗ[ZMod 2] W) where
  toFun g :=
    { toFun := fun f => (g : W →ₗ[ZMod 2] W) ∘ₗ f ∘ₗ (g.symm : W →ₗ[ZMod 2] W)
      map_zero' := by
        ext x
        simp
      map_add' := fun f f' => by
        ext x
        simp }
  map_one' := by
    ext f x
    rfl
  map_mul' g h := by
    ext f x
    rfl

@[expose] def burnsideB49x_muD :
    (W ≃ₗ[ZMod 2] W) →* AddMonoid.End (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) where
  toFun g :=
    { toFun := fun β => β.compl₁₂ (g.symm : W →ₗ[ZMod 2] W) (g.symm : W →ₗ[ZMod 2] W)
      map_zero' := by
        ext x y
        simp
      map_add' := fun β β' => by
        ext x y
        simp }
  map_one' := by
    ext β x y
    rfl
  map_mul' g h := by
    ext β x y
    rfl

variable {W}

theorem burnsideB49x_muN_apply (g : W ≃ₗ[ZMod 2] W) (f : W →ₗ[ZMod 2] W) (x : W) :
    burnsideB49x_muN W g f x = g (f (g.symm x)) := rfl

theorem burnsideB49x_muD_apply (g : W ≃ₗ[ZMod 2] W) (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (x y : W) : burnsideB49x_muD W g β x y = β (g.symm x) (g.symm y) := rfl

end Actions

end CFSG.ASVolI
