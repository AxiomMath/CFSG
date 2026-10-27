module

public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow6Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGL48TableBKnownFormsRestRkOpen7 : Prop :=
  GGL48TBForm1 ∧ GGL48TBForm2 ∧ (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab
      → LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGD4Three p lab → lab.n = 1 →
      LargeEvenLabelAll lab fun R _ I _ => GGIrredTableB p R I) ∧ GGL48TBForm4 ∧ GGL48TBForm5

end CFSG.StandardType
