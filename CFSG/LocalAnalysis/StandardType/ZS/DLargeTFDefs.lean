module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtMatrices
public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.StandardType.ZS

@[expose] def DLargeFourModel (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (A : Subgroup (U ≃ₗ[ZMod p] U)), p ≠ 2 → Module.finrank (ZMod p) U = 4 → ReflGen p A →
    AbsIrred p A → ¬ Quasithin.SimsG4.IsImprimitiveOnV A → QTwoLin.TransvectionFree A →
    (∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    IsOrthType p A ∨
      (DMax p A 4 ∧ ∃ (f : Module.Basis (Fin 4) (ZMod p) U) (t : ZMod p), t ^ 2 = -1 ∧
        (A = basisClosure f (weylN4Mats t) ∨ A = basisClosure f (weylEN4Mats t))) ∨
      (p ≠ 3 ∧ DMax p A 4 ∧ ∃ f : Module.Basis (Fin 4) (ZMod p) U,
        A = basisClosure f weylF4Mats) ∨
      (p ≠ 5 ∧ DMax p A 5 ∧ ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) U),
        α ^ 2 = α + 1 ∧ A = basisClosure f (h4BlockMats α))

end CFSG.StandardType.ZS

end
