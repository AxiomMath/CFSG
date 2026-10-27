module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45FieldFixOpenLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGLabelA2 lab ∧ p = 3

@[expose] def GGL45FieldFixKnownFormsOpen : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    GGL45FieldFixOpenLabel p lab → LargeEvenLabelAll lab (GGL45FieldFixKGRaw p lab)

end CFSG.StandardType
