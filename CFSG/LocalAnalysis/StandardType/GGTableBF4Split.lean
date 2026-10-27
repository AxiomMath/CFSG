module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem largeEvenLabelAll_tableB_F4_split {lab : LargeEvenLabel} (htag : lab.tag = .F4)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I :=
  largeEvenLabelAll_tableB_F4 htag hlab hp hpn fun _ => ggF4ThreeRankInput_holds

theorem ggBstarInputOn_F4_split : GGBstarInputOn GGTableBF4Label :=
  ggBstarInputOn_F4 ggF4ThreeRankInput_holds

theorem ggStdSubPreInputOn_F4_split : GGStdSubPreInputOn GGTableBF4Label :=
  ggStdSubPreInputOn_F4 ggF4ThreeRankInput_holds

end CFSG.StandardType
