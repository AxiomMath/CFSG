module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtendScalars
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Equalizer

public section

namespace CFSG.Walter

open Module TensorProduct

theorem finrank_invariants_extendScalars {F K G V : Type*} [Field F] [Field K] [Algebra F K]
    [Group G] [Finite G] [AddCommGroup V] [Module F V] (σ : Representation F G V) :
    finrank K (Theory.Representation.extendScalars K σ).invariants = finrank F σ.invariants := by
  classical
  have := Fintype.ofFinite G
  let f : V →ₗ[F] (G → V) := LinearMap.pi fun g => σ g - LinearMap.id
  have hf : σ.invariants = LinearMap.ker f := by
    ext v
    simp [f, funext_iff, sub_eq_zero]
  let fK : K ⊗[F] V →ₗ[K] (G → K ⊗[F] V) :=
    LinearMap.pi fun g => Theory.Representation.extendScalars K σ g - LinearMap.id
  have hfK : (Theory.Representation.extendScalars K σ).invariants = LinearMap.ker fK := by
    ext v
    simp [fK, funext_iff, sub_eq_zero]
  have hcomp : fK = (piRight F K K fun _ : G => V).toLinearMap ∘ₗ f.baseChange K := by
    ext v g
    simp [fK, f, tmul_sub]
  have hker : LinearMap.ker (f.baseChange K) = LinearMap.ker (AlgebraTensorModule.lTensor K K f) :=
    rfl
  rw [hfK, hcomp, LinearEquiv.ker_comp, hf, hker, ← (LinearMap.tensorKerEquiv K K f).finrank_eq,
    Module.finrank_baseChange]

end CFSG.Walter
