module

public import CFSG.LocalAnalysis.StandardType.GGNineDepCtx
public import CFSG.LocalAnalysis.StandardType.GGWAutDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGNineDepRowE7Input : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin (9 - 1) → V) (α : Fin (9 - 1) → Module.Dual (ZMod 3) V)
    (r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)) (T : Type) (s : T → (V ≃ₗ[ZMod 3] V)) (x : V)
    (X : GGNineDepCtx h α r s x),
    (Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 7 ∧
      GGWeylModel3 (CartanMatrix.E 7) (ggNineQ X)) → False

@[expose] def GGNineDepRowE8Input : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin (9 - 1) → V) (α : Fin (9 - 1) → Module.Dual (ZMod 3) V)
    (r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)) (T : Type) (s : T → (V ≃ₗ[ZMod 3] V)) (x : V)
    (X : GGNineDepCtx h α r s x),
    (Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 8 ∧
      GGWeylModel3 (CartanMatrix.E 8) (ggNineQ X)) → False

end CFSG.StandardType

end
