module

public import CFSG.LocalAnalysis.StandardType.GGNineDepRowExc
import CFSG.LocalAnalysis.StandardType.GGNineDepNegOne
import CFSG.LocalAnalysis.StandardType.GGNineDepWeylNeg

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggNineDepRowE7_holds : GGNineDepRowE7Input := by
  intro V _ _ h α r T s x X hX
  obtain ⟨hd, z, β, hz, hspan, hpair, hQ⟩ := hX
  refine ggNineDep_false_of_negEquiv_mem X (by omega) ?_
  rw [hQ]
  exact ggQ2WeylOf_neg_mem_E7 z β hz hspan hpair

theorem ggNineDepRowE8_holds : GGNineDepRowE8Input := by
  intro V _ _ h α r T s x X hX
  obtain ⟨hd, z, β, hz, hspan, hpair, hQ⟩ := hX
  refine ggNineDep_false_of_negEquiv_mem X (by omega) ?_
  rw [hQ]
  exact ggQ2WeylOf_neg_mem_E8 z β hz hspan hpair

end CFSG.StandardType

end
