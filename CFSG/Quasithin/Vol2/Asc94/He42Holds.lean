module

public import CFSG.Quasithin.Vol2.Asc94.HeK6
public import CFSG.Quasithin.Vol2.Asc94.He42P422Main
public import CFSG.Quasithin.Vol2.Asc94.He42P427

public section

namespace CFSG.Quasithin.A94

theorem he42_holds
    : He42 :=
  he42_of_inputs he42Input422_holds (he42Input426_of_422 he42Input422_holds)
      (he42Input427_holds he42Input422_holds)

theorem asc94K_of_he_order
    (hOrd : He_order) : CFSG.Quasithin.H13.Asc94_M24He_L52TypeK :=
  asc94K_of_he42' hOrd he42_holds

end CFSG.Quasithin.A94
