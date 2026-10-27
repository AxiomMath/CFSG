module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSL
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSLCent
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSLLevi

public section

namespace CFSG.StandardType

theorem ggRootCentOTwoTag_PSL : GGRootCentOTwoTag .PSL :=
  ggRootCentOTwoTag_PSL_of
    (fun _ K _ _ _ hm => ⟨KGPSL.radical (K := K) (Nat.le_of_succ_le hm),
      KGPSL.centralizer_rootInv_eq_sup hm, KGPSL.leviFull_le_normalizer_radical hm,
      KGPSL.disjoint_radical_leviFull hm, KGPSL.pCoreOf_centralizer_rootInv hm⟩)
    (fun _ _ _ _ _ hm hq _ hc _ hA₁ hA₂ _ hh hkey =>
      KGPSL.eq_one_of_conj_levi hm hq hc hA₁ hA₂ hh hkey)

end CFSG.StandardType
