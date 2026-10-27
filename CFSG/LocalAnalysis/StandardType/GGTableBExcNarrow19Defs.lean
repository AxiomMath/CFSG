module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcNarrow18Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGL48TableBKnownFormsRestRkOpen19 : Prop :=
  (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → ¬
      GGL48TableBVacLabel p lab → ¬ GGD4Three p lab → ¬ GGL48TB0TwRow p lab → ¬ GGL48TBTypeARow p
      lab → ¬ GGL48TBTwoARow p lab → ¬ GGL48TBTwistedARow p lab → ¬ GGL48TBExcInnRow p lab → ¬
      GGL48TBExcTwoRow p lab → ¬ GGL48TBE6Row p lab → LargeEvenLabelAll lab fun R _ I _ =>
      GGCoverPTableB p R I) ∧ GGL48TBForm4Rest16 ∧ GGL48TBForm5RowE

end CFSG.StandardType
