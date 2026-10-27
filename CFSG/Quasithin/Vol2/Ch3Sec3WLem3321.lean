module

public import CFSG.Quasithin.Vol2.Ch3Sec3WLem3321FH
public import CFSG.Quasithin.Vol2.Ch3Sec3WLem3321FSD

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace L3321

theorem step3_3_21f_ofW (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h14 : Stmt3_3_14)
    (hGA : GriessAllModelsStatement) (he : Step3_3_21e) (h15 : Step3_3_15R)
    (hC34 : CFSG.Quasithin.C134L32CorrM)
    (h12 : Step3_3_12R) (h20 : Stmt3_3_20) (hd : Step3_3_21d)
    (hfQ : Step3_3_21fQ) : Step3_3_21f := by
  intro G _ _ T M L D h ⟨e⟩ ⟨_, hmod⟩ hin
  rcases hmod with hext | hsum
  · exact false_of_inner_extW h7 h9 h14 hGA he h15 hC34 h20 hd hfQ h e hext hin
  · exact false_of_inner_sum_of_h12W h7 h14 hGA he h15 hC34 h12 h e hsum hin

end L3321

end CFSG.Quasithin.H13
