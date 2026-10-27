module

public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.StandardType.A6Red

open LinearMap (BilinForm)

@[expose] def ggA6SpFixed {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (A : Subgroup (V ≃ₗ[F] V)) : Submodule F V where
  carrier := {v | ∀ a ∈ A, a v = v}
  zero_mem' := fun a _ => map_zero a
  add_mem' := fun {v w} hv hw a ha => by rw [map_add, hv a ha, hw a ha]
  smul_mem' := fun c v hv a ha => by rw [map_smul, hv a ha]

@[expose] def ggA6SpFixer {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (B : BilinForm F V) (U : Submodule F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | g ∈ TauCeti.BilinForm.isometryGroup B ∧ ∀ u ∈ U, g u = u}
  one_mem' := ⟨(TauCeti.BilinForm.isometryGroup B).one_mem, fun _ _ => rfl⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨(TauCeti.BilinForm.isometryGroup B).mul_mem ha.1 hb.1, fun u hu => by
      show a (b u) = u
      rw [hb.2 u hu, ha.2 u hu]⟩
  inv_mem' := fun {a} ha =>
    ⟨(TauCeti.BilinForm.isometryGroup B).inv_mem ha.1, fun u hu => by
      show a.symm u = u
      conv_lhs => rw [← ha.2 u hu]
      exact a.symm_apply_apply u⟩

end CFSG.StandardType.A6Red
