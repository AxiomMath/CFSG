module

public import CFSG.Quasithin.Vol2.Ch10SecAShape
public import CFSG.Quasithin.Background.B4Statement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def Insp5aNonShape : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), B4Hyp G L →
    A38Types ↥L → ¬ Vol2.Ch10.SecA.IsShapeGroup ↥L →
      (∀ A : Subgroup (MulAut V), IsFFStarOffender G A → ¬ B42Conclusion G L A) ∧
        ¬ AsB45Table G L ∧ ¬ AsB45Part3 G L

end CFSG.Quasithin
