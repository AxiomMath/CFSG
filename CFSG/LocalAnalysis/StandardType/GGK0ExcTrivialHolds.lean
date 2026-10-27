module

public import CFSG.LocalAnalysis.StandardType.GGK0ExcTrivialOfTable

public section

namespace CFSG.StandardType.GGK0ExcB3Prod

theorem ggK0ExcTrivial_holds :
    GGK0ExcTrivial :=
  ggK0ExcTrivial_of_table fun _ _ hΛ hpair => ggKacValid_identityDatum hΛ hpair

end CFSG.StandardType.GGK0ExcB3Prod
