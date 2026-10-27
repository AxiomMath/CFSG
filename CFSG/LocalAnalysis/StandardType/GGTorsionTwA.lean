module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
import CFSG.LocalAnalysis.StandardType.GGTorsionPSUComp
import CFSG.LocalAnalysis.StandardType.GGTorsionClassical
import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp
import CFSG.LocalAnalysis.StandardType.GGTorsionLinear
import CFSG.LocalAnalysis.StandardType.GGTorsionTwF4
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionTwA

theorem ggTorsionKnownOver_typeTwA :
    GGTorsionKnownOver fun lab => lab.tag = .twA := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have htag : lab.tag = .twA := by
    obtain ⟨R, _, I, F, -, -, θ, hP, -⟩ := largeEvenRawDatum_exists hraw
    exact hP
  obtain ⟨t, r, n⟩ := lab
  obtain rfl : t = .twA := htag
  obtain ⟨hn, hr1, hr2⟩ := hlab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, _, _, hK, hs, hna, θ, -, hI⟩ := hraw
  have hδp' : ggInducedAut θ δ ^ p = 1 := by rw [← map_pow, hδp, map_one]
  have hJ' := ggTorsion_isComponentOf_image θ hcomp
  obtain ⟨t', n', f', hL⟩ := ggTorsion_psu_components hn hr1 hr2 hK hp hp2 hδp' hI hJ'
  obtain ⟨e₂⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
  exact ggTorsion_not_marking_of_classical
    (Or.inl ⟨t', n', f', CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e₂.symm hL⟩) hJ

theorem ggTorsionKnownOver_ambA :
    GGTorsionKnownOver GGTorsionAmbA :=
  ggTorsionKnownOver_or ggTorsionKnownOver_typeA ggTorsionKnownOver_typeTwA

end TorsionTwA

end CFSG.StandardType
