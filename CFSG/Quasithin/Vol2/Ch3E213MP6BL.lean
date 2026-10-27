module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CB

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp minorAut)
open CFSG.Blueprint (suzukiGroup)

variable {k : Type} [Field k]

@[expose] def subfieldSz (F₀ : Subfield k) (a : ℕ) : Subgroup (antiSp k) :=
  ((suzukiGroup a ↥F₀).subgroupOf (antiSp ↥F₀)).map (subAntiSp F₀)

end CFSG.Quasithin.Ch3E213M
