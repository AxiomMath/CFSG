module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLDvdNarrow14Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGL48TBTwoARow (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ 3 ≤ lab.rank ∧ lab.n = 1 ∧ p = 3

@[expose] def GGL48TableBKnownFormsRestRkOpen15 : Prop :=
  (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → ¬
      GGL48TableBVacLabel p lab → ¬ GGD4Three p lab → ¬ GGL48TB0TwRow p lab → ¬ GGL48TBTypeARow p
      lab → ¬ GGL48TBTwoARow p lab → LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R
      I) ∧ (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → ¬ GGL48TB0TwRow p lab → ¬ GGL48TBTypeARow
      p lab → LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I) ∧ GGL48TBForm5RowE

end CFSG.StandardType
