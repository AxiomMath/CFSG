module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Fin
import CFSG.GroupTheory.ThreeTranspositions.Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem fischerStronglyThreeEmbedded_holds : FischerStronglyThreeEmbedded :=
  fun A _ _ H H₀ t hH₀ hr hY hS hne htH ht2 htK =>
    CFSG.GroupTheory.ThreeTranspositions.exists_sq_cube_not_mem_relPPrimeCore
      CFSG.GroupTheory.ThreeTranspositions.noThreeTranspositionClass A H H₀ t hH₀ hr hY hS hne
      htH ht2 htK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
