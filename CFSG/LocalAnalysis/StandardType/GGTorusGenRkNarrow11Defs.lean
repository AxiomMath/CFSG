module

public import CFSG.LocalAnalysis.StandardType.GGCoverRkNarrow10Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGL48TBForm5RowE : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGL48TB0TwRowE p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableBRk p R I (GGL48TB0Rank lab)

@[expose] def GGL48TableBKnownFormsRestRkOpen11 : Prop :=
  GGL48TBForm1 ∧ GGL48TBForm4 ∧ GGL48TBForm5RowE

end CFSG.StandardType
