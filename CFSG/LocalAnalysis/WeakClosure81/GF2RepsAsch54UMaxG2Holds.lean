module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxG2

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxG2Core
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxG2Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem asch80G2Prime_holds : Asch80G2Prime := by
  intro Y _ _ E T r hEn hr hr2 hE hC hT
  exact Asch80G2.not_hasUniqueMaxOver_of_gen hEn hr hr2 hE hC hT
    fun _ _ hz hz' hz1 hz1' hne hc hZ =>
      Asch80G2.g2_sup_centralizer_eq_top hr hr2 hE hz hz' hz1 hz1' hne hc hZ

end CFSG.LocalAnalysis.WeakClosure81

end
