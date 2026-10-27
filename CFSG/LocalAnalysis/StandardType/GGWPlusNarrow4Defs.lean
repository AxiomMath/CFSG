module

public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow3Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL48TableBKnownFormsRestRkOpen4 : Prop :=
  GGL48TBForm1 ∧ GGL48TBForm2 ∧ (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab
      → LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGD4Three p lab → LargeEvenLabelAll lab
      fun R _ I _ => GGIrredTableB p R I) ∧ GGL48TBForm4 ∧ GGL48TBForm5 ∧ (∀ (p : ℕ) (lab :
      LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → ¬
      GGL48TableBVacLabel p lab → GGL48TB0TwRow p lab → LargeEvenLabelAll lab fun R _ I _ =>
      GGIrredModTableBRk p R I (GGL48TB0Rank lab) ∨ GGWPlusTableBRk p R I (GGL48TB0Rank lab))

end CFSG.StandardType
