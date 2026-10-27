module

public import CFSG.LocalAnalysis.StandardType.GGNineDepCtx
public import CFSG.LocalAnalysis.StandardType.GGWAutDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGNineDepRowImprimInput : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin (9 - 1) → V) (α : Fin (9 - 1) → Module.Dual (ZMod 3) V)
    (r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)) (T : Type) (s : T → (V ≃ₗ[ZMod 3] V)) (x : V)
    (X : GGNineDepCtx h α r s x),
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV (ggNineQ X) → False

end CFSG.StandardType

end
