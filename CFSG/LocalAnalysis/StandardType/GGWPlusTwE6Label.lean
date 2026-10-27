module

public import CFSG.LocalAnalysis.StandardType.GGWPlusTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem largeEvenLabelAll_wplusRk_twE6_three
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twE6)
    (h3 : 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGWPlusTableBRk 3 R I 6 := by
  have hn : 1 ≤ lab.n := hlab.1
  exact TwE6Delta.labelAll ht fun K _ _ hK => ggWPlusTableBRk_twE6_three lab.n hn hK h3

end CFSG.StandardType
