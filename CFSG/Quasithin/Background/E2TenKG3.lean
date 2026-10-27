module

public import CFSG.Foundations.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.E2

@[expose] def KGI22One : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → Subgroup.center K ≠ ⊥ →
    IsPGroup 2 (Subgroup.center K) →
    (Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 5)) →
      Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) ∧
    (Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) →
      Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 2)))

end CFSG.Quasithin.E2
