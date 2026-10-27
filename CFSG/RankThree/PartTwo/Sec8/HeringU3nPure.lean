module

public import CFSG.RankThree.PartTwo.Sec8.HeringU3nUnitary
public import CFSG.RankThree.PartTwo.Sec8.Item84PairProofAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG.RankThree.PartTwo.Sec8.HeringU3n


theorem pair86LocalCentral_of_pure (hPure : U3nPure) (h45 : Sec4.Item4_5)
    (hPU : Pair84PartnerU) : Pair86LocalCentral :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hset => (local_of_pure hPure h45 hPU hset).1

theorem pair86LocalOmega_of_pure (hPure : U3nPure) (h45 : Sec4.Item4_5)
    (hPU : Pair84PartnerU) : Pair86LocalOmega :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hset => (local_of_pure hPure h45 hPU hset).2

theorem pair86NonUnitary_of_pure (h310 : Sec6.Item3_10) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (hPU : Pair84PartnerU) (hPure : U3nPure) : Pair86NonUnitary :=
  pair86NonUnitary_of h310 h45 h48 (pair86LocalCentral_of_pure hPure h45 hPU)
    (pair86LocalOmega_of_pure hPure h45 hPU)

theorem pair86NonUnitary_of_3_10 (h310 : Sec6.Item3_10) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (hPU : Pair84PartnerU) : Pair86NonUnitary :=
  pair86NonUnitary_of_pure h310 h45 h48 hPU u3nPure_holds

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof

namespace CFSG.RankThree.PartTwo.Sec8

open Item86ResProof


theorem pair86NonUnitary_of_gamma (h310 : Sec6.Item3_10) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h418 : Item418Theta) (hUL : Pair84GammaUL) (hNL : Pair84GammaNL)
    (hRee : Pair84GammaRee) : Pair86NonUnitary :=
  pair86NonUnitary_of_3_10 h310 h45 h48 (pair84PartnerU_of_gamma h45 h418 hUL hNL hRee)

end CFSG.RankThree.PartTwo.Sec8
