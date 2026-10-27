module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofU42
public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofA9
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3PlusInn
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcRed
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Four
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcInner
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3Inner
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3Minus

public section

namespace CFSG.RankThree.PartTwo.Sec21

section Certs


theorem item211ResidualLie_of_kfacts₂ (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hExcP : KS211ExcPlus) (hExcM : KS211ExcMinus) (hL3P : KS211L3Plus) :
    Item211ResidualLie :=
  item211ResidualLie_of (item211LiePlusU42_of h45 h66 ks211U42CharThree_holds)
      (item211LiePlusExc_of h45 h66 ks211ExcInner_holds hExcP) (item211LiePlusA9_of h45 h66)
      (item211LiePlusL3_of h45 h66 ks211L3Inner_holds hL3P)
      (item211LieMinusL3_of h45 h66 ks211L3Inner_holds ks211L3Minus_holds)
      (item211LieMinusU42_of h45 h66 ks211U42FourGroup_holds) (item211LieMinusA9_of h45 h66)
      (item211LieMinusExc_of h45 h66 ks211ExcInner_holds hExcM)

theorem item211ResidualLie_of_models (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hPG2 : KS211ExcPlusG2) (hPSp : KS211ExcPlusSp) (hPU4 : KS211ExcPlusU4)
    (hPL4 : KS211ExcPlusL4) (hMG2 : KS211ExcMinusG2) (hMSp : KS211ExcMinusSp)
    (hMU4 : KS211ExcMinusU4) (hML4 : KS211ExcMinusL4) (hL : KS211L3PlusLinearOuter)
    (hU : KS211L3PlusUnitaryCore) : Item211ResidualLie :=
  item211ResidualLie_of_kfacts₂ h45 h66 (ks211ExcPlus_of_models hPG2 hPSp hPU4 hPL4)
    (ks211ExcMinus_of_models hMG2 hMSp hMU4 hML4)
    (ks211L3Plus_of_cores (ks211L3PlusLinearCore_of_outer hL) hU)

end Certs

end CFSG.RankThree.PartTwo.Sec21
