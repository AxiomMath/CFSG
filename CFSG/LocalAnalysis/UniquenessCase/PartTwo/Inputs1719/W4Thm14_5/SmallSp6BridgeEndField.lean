module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6BridgeFactors

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge

open Representation Module CFSG.Theory.Representation
open scoped TensorProduct MonoidAlgebra

variable {G W : Type} [Group G] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible]

variable (k : Type) [Field k]
  [Algebra (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k] [Algebra (ZMod 2) k]
  [IsScalarTower (ZMod 2) (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k]

@[expose] noncomputable def binaryAsModuleRep : Representation (ZMod 2) G ρ.asModule where
  toFun g := (CFSG.endFieldRep ρ g).restrictScalars (ZMod 2)
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp

@[expose] noncomputable def binaryAsModuleEquiv :
    Representation.Equiv ρ (binaryAsModuleRep ρ) :=
  Representation.Equiv.mk ρ.asModuleEquiv.symm fun g => by
    apply LinearMap.ext
    intro w
    change ρ.asModuleEquiv.symm (ρ g w) =
      CFSG.endFieldRep ρ g (ρ.asModuleEquiv.symm w)
    rw [CFSG.endFieldRep_apply]
    simp
    rfl

@[expose] noncomputable def endFieldTensorMap :
    IntertwiningMap (extendScalars k (binaryAsModuleRep ρ))
      (extendScalars k (CFSG.endFieldRep ρ)) :=
  { toLinearMap := TensorProduct.mapOfCompatibleSMul
      (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) (ZMod 2) k k ρ.asModule
    isIntertwining' g := by
      apply LinearMap.ext
      intro u
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul a w =>
        change TensorProduct.mapOfCompatibleSMul
            (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) (ZMod 2) k k ρ.asModule
            (a ⊗ₜ[ZMod 2] binaryAsModuleRep ρ g w) =
          extendScalars k (CFSG.endFieldRep ρ) g
            (TensorProduct.mapOfCompatibleSMul
              (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) (ZMod 2) k k ρ.asModule
              (a ⊗ₜ[ZMod 2] w))
        rw [TensorProduct.mapOfCompatibleSMul_tmul, TensorProduct.mapOfCompatibleSMul_tmul,
          extendScalars_apply, LinearMap.baseChange_tmul]
        rfl
      | add u v hu hv => simpa using congrArg₂ (· + ·) hu hv }

theorem endFieldTensorMap_surjective : Function.Surjective (endFieldTensorMap ρ k) :=
  TensorProduct.mapOfCompatibleSMul_surjective
    (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) (ZMod 2) k k ρ.asModule

@[expose] noncomputable def endFieldExtensionSurjection :
    IntertwiningMap (extendScalars k ρ) (extendScalars k (CFSG.endFieldRep ρ)) :=
  (endFieldTensorMap ρ k).comp
    (extendScalars_map k (binaryAsModuleEquiv ρ).toIntertwiningMap)

theorem endFieldExtensionSurjection_surjective :
    Function.Surjective (endFieldExtensionSurjection ρ k) := by
  apply (endFieldTensorMap_surjective ρ k).comp
  change Function.Surjective (ρ.asModuleEquiv.symm.toLinearMap.baseChange k)
  exact LinearMap.baseChange_surjective k ρ.asModuleEquiv.symm.surjective

theorem factorsFinrankLe_endField_extension_comp {H : Type} [Group H] (π : H →* G)
    {n : ℕ} (h : FactorsFinrankLe ((extendScalars k ρ).comp π) n) :
    FactorsFinrankLe ((extendScalars k (CFSG.endFieldRep ρ)).comp π) n := by
  let f : IntertwiningMap ((extendScalars k ρ).comp π)
      ((extendScalars k (CFSG.endFieldRep ρ)).comp π) :=
    ⟨(endFieldExtensionSurjection ρ k).toLinearMap, fun h =>
      (endFieldExtensionSurjection ρ k).isIntertwining' (π h)⟩
  have hf : Function.Surjective f := endFieldExtensionSurjection_surjective ρ k
  exact factorsFinrankLe_of_surjective f hf h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge
