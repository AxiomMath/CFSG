module

public import CFSG.Quasithin.Vol2.Ch10SecQ2E3
public import CFSG.Quasithin.Vol2.Ch10SecFMain
public import CFSG.Quasithin.Vol2.Ch10SecB5Easy

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem stmt10_2_1_of
    (h3210 : Ch10.TmpL6_3_2_10_eight) (h1012 : Ch10.Stmt10_1_2) (he23 : E2.E23Statement)
    (he234 : E2.E23FourStatement) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (hC58 : TheoremC58) (h331 : Stmt3_3_1) (h113 : ASInputs.AS_C_1_13)
    (h1013 : Ch10.Stmt10_1_3) (hO1 : SecF.Obl10_2_1E4HStar) (hO2 : SecF.Obl10_2_1E4A314) :
    Ch10.Stmt10_2_1 := by
  intro G _ _ T L I hyp hn3
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)
  · exact normalizer_baum_le_of_thompsonJ h3210 hyp hJ
  have h311 := theorem311Stmt_of_C58 hC58
  rcases SecB.cases123_of_not_thompsonJ h1012 hyp hJ with ⟨n, h1⟩ | h2 | h3
  · exact normalizer_baum_le_case1 he23 h37 h38 h322 hshape h3228 h311 h331 hyp h1 hJ
  · by_cases hCZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥
    · exact normalizer_baum_le_case2_eq he23 he234 h37 h38 h322 hshape h3228 h331 h113 hyp h2 hJ
        hCZ
    · exact SecF.normalizer_baum_le_case2_ne he23 he234 h37 h38 h39 h322 hshape h3228 h311 h331
        h113 h1013 hO1 hO2 hyp h2 hJ hCZ
  · exact absurd h3 hn3

end CFSG.Quasithin.Vol2.Ch10.SecE
