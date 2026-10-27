module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
import CFSG.LocalAnalysis.StandardType.GGTorsionBC
import CFSG.LocalAnalysis.StandardType.GGTorsionOrth
import CFSG.LocalAnalysis.StandardType.GGTorsionTwF4
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionBCDClass

theorem ggTorsionKnownOver_ambBCD :
    GGTorsionKnownOver GGTorsionAmbBCD := by
  have h := ggTorsionKnownOver_or
    (ggTorsionKnownOver_or ggTorsionKnownOver_typeBC ggTorsionKnownOver_typeD)
    ggTorsionKnownOver_typeTwD
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  refine h p X hX δ J ⟨hp, hp2, hδp, hδ1, hcomp, hXc, lab, hlab, ?_⟩ hJ
  refine largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hs, hna, θ, hP, hI⟩
  refine ⟨hs, hna, θ, ?_, hI⟩
  unfold GGTorsionAmbBCD at hP
  tauto

end TorsionBCDClass

end CFSG.StandardType
