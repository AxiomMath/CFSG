module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionExcDefs

@[expose] def GGTorsionKnownOverTags (P T : LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    ∀ (δ : MulAut X) (J : Subgroup X), GGTorsionDatum P p δ J →
      ¬ LargeEvenMarking J fun lab _ _ _ _ _ => T lab

@[expose] def GGExcNoF4Known : Prop :=
  GGTorsionKnownOverTags
    (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (fun lab => lab.tag = .F4)

end TorsionExcDefs

end CFSG.StandardType
