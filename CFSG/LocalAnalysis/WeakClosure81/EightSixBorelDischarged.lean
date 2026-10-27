module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfHolds
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorel
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFour
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T E : Subgroup G}

theorem w3Borel86_of_split_discharged (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H)
    (hfact : Orth6MinusOddTranspFact) : W3Borel86 G :=
  w3Borel86_of_split spURootConfiguration_holds h711 w3Lem85TwoGap4_holds
    (w3Lem85TwoGap6_of_fact hfact)

end CFSG.LocalAnalysis.WeakClosure81

end
