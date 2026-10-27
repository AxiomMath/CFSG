module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionClasses

theorem ggTorsionKnown_of_classes (hA : GGTorsionKnownOver GGTorsionAmbA)
    (hB : GGTorsionKnownOver GGTorsionAmbBCD) (hE : GGTorsionKnownOver GGTorsionAmbExc)
    (hS : GGTorsionKnownOver GGTorsionAmbSmall) : GGTorsionKnown := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have hcls : GGTorsionAmbA lab ∨ GGTorsionAmbBCD lab ∨ GGTorsionAmbExc lab ∨
      GGTorsionAmbSmall lab := by
    obtain ⟨t, r, n⟩ := lab
    cases t <;> simp [GGTorsionAmbA, GGTorsionAmbBCD, GGTorsionAmbExc, GGTorsionAmbSmall]
  have key : ∀ P : LargeEvenLabel → Prop, P lab → GGTorsionDatum P p δ J := by
    intro P hP
    refine ⟨hp, hp2, hδp, hδ1, hcomp, hXc, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, -, hI⟩
    exact ⟨hs, hna, θ, hP, hI⟩
  rcases hcls with h | h | h | h
  · exact hA p X hX δ J (key _ h) hJ
  · exact hB p X hX δ J (key _ h) hJ
  · exact hE p X hX δ J (key _ h) hJ
  · exact hS p X hX δ J (key _ h) hJ

end TorsionClasses

end CFSG.StandardType
