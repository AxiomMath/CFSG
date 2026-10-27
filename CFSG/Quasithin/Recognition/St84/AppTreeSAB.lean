module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.F112HypW
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivCard
public import CFSG.Quasithin.Recognition.St84.L2Group

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
  CFSG.Quasithin.St84 CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem f112sa_bigB_le_normalizer_L2 {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set H) :=
  sup_le (sup_le hF.1.h2.borel_le
    ((F1.borelOf_le L2 S).trans Subgroup.le_normalizer)) hF.1.h2.normalizes

end CFSG.Quasithin.F112R.St84
