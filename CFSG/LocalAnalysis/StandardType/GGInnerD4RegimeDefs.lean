module

public import CFSG.LocalAnalysis.StandardType.GGB36StepThreeInputs
public import CFSG.LocalAnalysis.StandardType.GGInnerD4Regimes
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGInnerOnD4RA : Prop :=
  GGInnerOnD4On fun lab => GGKacRA lab 3

@[expose] def GGInnerOnD4DGen : Prop :=
  GGInnerOnD4On fun lab => (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank

@[expose] def GGInnerOnD4Small : Prop :=
  GGInnerOnD4On fun lab =>
    lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨
      lab.tag = .G2der ∨ lab.tag = .twF4der

theorem ggInnerOnD4_iff :
    GGInnerOnD4 ↔ GGInnerOnD4On fun lab => ¬ (lab.tag = .E6 ∨ lab.tag = .twE6) := Iff.rfl

end CFSG.StandardType

end
