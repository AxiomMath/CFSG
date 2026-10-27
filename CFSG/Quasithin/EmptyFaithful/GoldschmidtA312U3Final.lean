module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Bridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3B6Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Small
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Psu3

public section

namespace CFSG.Quasithin.A312U3

theorem su3OddIrr_holds
    : SU3OddIrr :=
  su3OddIrr_of (su3OddIrrGe7_of su3NoPSL3_holds su3PSU3Case_holds su3NoPSL2_holds)
    su3OddIrrSmall_holds

theorem su3OddIrr_A38c17_holds
    : CFSG.Quasithin.A38c17.SU3OddIrr :=
  su3OddIrr_A38c17_of su3OddIrr_holds

end CFSG.Quasithin.A312U3
