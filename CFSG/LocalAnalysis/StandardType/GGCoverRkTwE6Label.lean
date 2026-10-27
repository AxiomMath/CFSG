module

public import CFSG.LocalAnalysis.StandardType.GGCoverRkTwE6
public import CFSG.LocalAnalysis.StandardType.GGWPlusTwE6Label

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem largeEvenLabelAll_coverPRk_twE6_three
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twE6)
    (h3 : 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableBRk 3 R I 6 := by
  have hn : 1 ≤ lab.n := hlab.1
  exact TwE6Delta.labelAll ht fun K _ _ hK => ggCoverPTableBRk_twE6_three lab.n hn hK h3

end CFSG.StandardType
