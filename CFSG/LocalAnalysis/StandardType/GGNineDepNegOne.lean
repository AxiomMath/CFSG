module

public import CFSG.LocalAnalysis.StandardType.GGNineDepCtx
import CFSG.LocalAnalysis.StandardType.GGNineDepNegLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggNineDep_false_of_negEquiv_mem {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin (9 - 1) → V} {α : Fin (9 - 1) → Module.Dual (ZMod 3) V}
    {r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)} {T : Type} {s : T → (V ≃ₗ[ZMod 3] V)} {x : V}
    (X : GGNineDepCtx h α r s x) (hd : Module.finrank (ZMod 3) ↥(ggFixLineT r s) ≤ 8)
    (hneg : (LinearEquiv.neg (ZMod 3) : ↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s)) ∈
      ggNineQ X) : False :=
  ggNineDep_false_of_neg_mem X hd hneg fun v => LinearEquiv.neg_apply v

end CFSG.StandardType

end
