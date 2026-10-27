module

public import CFSG.Quasithin.Recognition.CertTitsOutPairs
public import CFSG.Quasithin.Recognition.CertTwoF4AmalgamLocal

public section

namespace CFSG.Quasithin

theorem titsOutBound
    : TitsOutBound := titsOuter_card_le_two

theorem twoF4AmalgamLocal
    : TwoF4AmalgamLocal := twoF4AmalgamLocal_of_outBound titsOutBound

end CFSG.Quasithin
