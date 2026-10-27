module

public import TauCeti.RingTheory.RootsOfUnity.ZMod

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

variable {L : Type*} [Field L]

@[expose] def rootsOfUnityAddHom (p : ℕ) :
    Additive (rootsOfUnity p L) →+ Additive Lˣ where
  toFun x := Additive.ofMul (x.toMul : Lˣ)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem rootsOfUnityAddHom_injective (p : ℕ) :
    Function.Injective (rootsOfUnityAddHom (L := L) p) := by
  intro x y hxy
  apply Additive.ext
  apply Subtype.ext
  simpa [rootsOfUnityAddHom] using congrArg Additive.toMul hxy

@[expose] def zmodToUnits (p : ℕ) [NeZero p] (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ p) :
    ZMod p →+ Additive Lˣ :=
  (rootsOfUnityAddHom (L := L) p).comp hζ.zmodEquivRootsOfUnity.toAddMonoidHom

theorem zmodToUnits_injective (p : ℕ) [NeZero p] (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (zmodToUnits (L := L) p ζ hζ) :=
  (rootsOfUnityAddHom_injective (L := L) p).comp hζ.zmodEquivRootsOfUnity.injective

end CFSG.LieType.AlgebraicGroups
