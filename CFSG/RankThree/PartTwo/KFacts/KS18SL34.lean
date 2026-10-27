module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KS18SL34 : Prop :=
  ∀ (X : Type) [Group X] [Finite X]
    (φ : X →* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) (N : Subgroup X) [N.Normal],
    IsPGroup 2 N → φ.ker ≤ N → IsEmpty (X ⧸ N ≃* projSL 3 (GaloisField 2 2))

end CFSG.RankThree.PartTwo.KFacts
