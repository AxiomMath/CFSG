module

public import CFSG.Quasithin.Vol2.Ch10SecE22Two
public import CFSG.Quasithin.Vol2.Ch10SecF22
public import CFSG.Quasithin.Vol2.Ch10SecB5Easy
public import CFSG.Quasithin.Vol2.Ch10SecE22OneB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem stmt10_2_2_of
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h1012 : Ch10.Stmt10_1_2) (h1021 : Ch10.Stmt10_2_1) (he23 : E2.E23Statement)
    (h322 : Ch10.TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape) (hO2 : SecF.Obl10_2_1E4A314)
    (hO3 : SecF.Obl10_2_2FourS5) : Ch10.Stmt10_2_2 := by
  intro G _ _ T L I hyp H hH hZH
  obtain ⟨h1, hJ⟩ := stmt10_2_2_one hC58 h317 h37 h38 h331 h3228 h1012 hyp hH hZH
  refine ⟨h1, fun h12 => ⟨stmt10_2_2_two h1021 h331 hyp hH hZH (SecB.not_case3_of_case12 h12),
    fun ⟨_, h1'⟩ => stmt10_2_2_three he23 h37 h38 h322 hshape h3228 hyp h1' hJ,
    SecF.stmt10_2_2_four (theorem311Stmt_of_C58 hC58) h331 hO2 hO3 hyp hH hZH h12⟩⟩

end CFSG.Quasithin.Vol2.Ch10.SecE
