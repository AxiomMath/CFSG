module

public import CFSG.Quasithin.Vol2.Ch6Inputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS

public section

namespace CFSG.Quasithin.H13

theorem ch6InE63_of (h : ASInputs.AS_E_6_3) : Ch6InE63 :=
  fun G _ _ T M V hE hV hm => h G T M V hV hE hm

end CFSG.Quasithin.H13
