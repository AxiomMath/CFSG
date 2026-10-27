module

public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow8Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGL48TB0TwRowE (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1

@[expose] def GGL48TableBKnownFormsRestRkOpen9 : Prop :=
  GGL48TBForm1 ∧ (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGL48TB0TwRowE p lab → LargeEvenLabelAll
      lab fun R _ I _ => GGCoverPTableBRk p R I (GGL48TB0Rank lab)) ∧ GGL48TBForm4 ∧ GGL48TBForm5

end CFSG.StandardType
