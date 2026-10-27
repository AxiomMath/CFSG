module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Splitting
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.ActionAbs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Klein
import CFSG.Quasithin.Background.BlueprintB2Defs

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

namespace StdCfg

private theorem cert14951_swap_zero_one_mem_Eset : Equiv.swap (0 : Fin 5) 1 ∈ Eset := by
  decide +kernel

private theorem cert14951_swap_two_three_mem_Eset : Equiv.swap (2 : Fin 5) 3 ∈ Eset := by
  decide +kernel

end StdCfg

end CFSG.QuasithinUnique.A5

namespace Certificates

theorem certificate14951 : Equiv.swap (0 : Fin 5) 1 ∈ CFSG.QuasithinUnique.A5.Delta5.Eset ∧
    Equiv.swap (2 : Fin 5) 3 ∈ CFSG.QuasithinUnique.A5.Delta5.Eset := by
  exact ⟨CFSG.QuasithinUnique.A5.StdCfg.cert14951_swap_zero_one_mem_Eset,
    CFSG.QuasithinUnique.A5.StdCfg.cert14951_swap_two_three_mem_Eset⟩

end Certificates
