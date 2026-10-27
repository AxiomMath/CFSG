module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] noncomputable def co1Act : Representation (ZMod 2) Co1 (Fin 24 → ZMod 2) where
  toFun g := Matrix.mulVecLin (g : Matrix (Fin 24) (Fin 24) (ZMod 2))
  map_one' := by
    simp only [Units.val_one, Submonoid.coe_one, Matrix.mulVecLin_one]
    rfl
  map_mul' g h := by
    simp only [Units.val_mul, Submonoid.coe_mul, Matrix.mulVecLin_mul]
    rfl

@[expose] def Co1ModuleUniqueness : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V], Module.finrank (ZMod 2) V = 24 →
    ∀ ρ : Representation (ZMod 2) Co1 V, ρ ≠ 1 →
      ∃ ψ : V ≃ₗ[ZMod 2] (Fin 24 → ZMod 2), ∀ g v, ψ (ρ g v) = co1Act g (ψ v)

end CFSG.Monster.GMS
