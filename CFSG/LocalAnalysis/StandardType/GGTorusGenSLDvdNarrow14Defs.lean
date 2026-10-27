module

public import CFSG.LocalAnalysis.StandardType.GGCoverSLNarrow13Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGL48TableBKnownFormsRestRkOpen14 : Prop :=
  (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → ¬
      GGL48TableBVacLabel p lab → ¬ GGD4Three p lab → ¬ GGL48TB0TwRow p lab → ¬ GGL48TBTypeARow p
      lab → LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R
      I) ∧ (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → ¬ GGL48TB0TwRow p lab → ¬ GGL48TBTypeARow
      p lab → LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I) ∧ GGL48TBForm5RowE

end CFSG.StandardType
