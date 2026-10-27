module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkCoprimeNarrow16Defs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoTableB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGL48TBForm4RestSymp : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → ¬ GGL48TB0TwRow p lab →
        ¬ GGL48TBTypeARow p lab → ¬ GGL48TBTwistedARow p lab → ¬ GGTableBSympLabel p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I

end CFSG.StandardType
