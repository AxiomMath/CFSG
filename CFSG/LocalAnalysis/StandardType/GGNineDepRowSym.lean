module

public import CFSG.LocalAnalysis.StandardType.GGNineDepCtx
public import CFSG.LocalAnalysis.StandardType.GGWAutDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGNineDepRowSymSuccInput : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin (9 - 1) → V) (α : Fin (9 - 1) → Module.Dual (ZMod 3) V)
    (r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)) (T : Type) (s : T → (V ≃ₗ[ZMod 3] V)) (x : V)
    (X : GGNineDepCtx h α r s x),
    (¬ 3 ∣ Module.finrank (ZMod 3) ↥(ggFixLineT r s) + 1 ∧
      ∃ e : ↥(ggNineQ X) ≃* Equiv.Perm (Fin (Module.finrank (ZMod 3) ↥(ggFixLineT r s) + 1)),
        ∀ q : ↥(ggNineQ X), GGLinRefl (q : ↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s)) →
          ∃ i j, i ≠ j ∧ e q = Equiv.swap i j) → False

@[expose] def GGNineDepRowSymSuccTwoInput : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin (9 - 1) → V) (α : Fin (9 - 1) → Module.Dual (ZMod 3) V)
    (r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)) (T : Type) (s : T → (V ≃ₗ[ZMod 3] V)) (x : V)
    (X : GGNineDepCtx h α r s x),
    (3 ∣ Module.finrank (ZMod 3) ↥(ggFixLineT r s) + 2 ∧
      ∃ e : ↥(ggNineQ X) ≃* Equiv.Perm (Fin (Module.finrank (ZMod 3) ↥(ggFixLineT r s) + 2)),
        ∀ q : ↥(ggNineQ X), GGLinRefl (q : ↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s)) →
          ∃ i j, i ≠ j ∧ e q = Equiv.swap i j) → False

end CFSG.StandardType

end
