module

public import CFSG.Quasithin.Vol2.Ch9Sec3FactsFF
public import CFSG.Quasithin.Vol2.Ch9Sec3FFCLie

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin


theorem a314InnerLieFact_holds : A314InnerLieFact := by
  intro Y _ _ _ T B L D hT hB _ hL hBL _ hLn hLie hD3 hDL hDT hTB
  exact FFC.le_normalizer_of_inner_lie hT hB hL hBL hLn hLie hD3 hDL hDT hTB

end CFSG.Quasithin.H13.Ch9
