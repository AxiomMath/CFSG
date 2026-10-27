module

public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGCentre
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenLabelAll_centerPrime_clD
    {lab : LargeEvenLabel} {p : ℕ}
    (hlab : LargeEvenInLambda2 lab) (hgen : GGKacGenericClD lab p) :
    LargeEvenLabelAll lab fun R _ _ _ => GGCenterPrime p R := by
  obtain ⟨hgen, htag, h4⟩ := hgen
  have hp : p.Prime := hgen.1
  have hp2 : p ≠ 2 := hgen.2.1
  rcases htag with ht | ht
  · exact largeEvenLabelAll_centerPrime_omegaPlus ht h4 hp hp2
  · refine largeEvenLabelAll_omegaMinus ht h4 ?_
    intro K _ _ _ hK b c hbc
    exact CorFourTwoOpen.ggCenterPrime_omegaMinus hp hp2 (by omega) hbc

end CFSG.StandardType

end
