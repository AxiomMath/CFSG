module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkNarrow11Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGL48TBTorusARow (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ lab.rank + 1

@[expose] def GGL48TableBKnownFormsRestRkOpen12 : Prop :=
  GGL48TBForm1 ∧ (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → ¬ GGL48TB0TwRow p lab → ¬
      GGL48TBTorusARow p lab → LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R
      I) ∧ GGL48TBForm5RowE

end CFSG.StandardType
