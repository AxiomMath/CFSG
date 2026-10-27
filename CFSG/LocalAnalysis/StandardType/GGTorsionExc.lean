module

public import CFSG.LocalAnalysis.StandardType.GGTorsionExcDefs
public import CFSG.LocalAnalysis.StandardType.GGTorsionExcField
import CFSG.LocalAnalysis.StandardType.GGTorsionExcE8
import CFSG.LocalAnalysis.StandardType.GGTorsionExcF4Low
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionExc

theorem ggTorsionKnownOver_exc_of_noF4
    (hF4 : GGExcNoF4Known) : GGTorsionKnownOver GGTorsionAmbExc := by
  intro p X _ _ hX δ J hdat hJ
  have hJ' : LargeEvenMarking J fun lab _ _ _ _ _ =>
      (lab.tag = .E8 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der) ∨ lab.tag = .F4 :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h => by
      simp only [GGL45TorsionTag] at h
      tauto) hJ
  rcases largeEvenMarking_or hJ' with h1 | h2
  · exact ggTorsionKnownOver_excE8Sr p X hX δ J hdat h1
  · obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
    have hmark' : LargeEvenMarking X fun lab _ _ I _ θ =>
        ((lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧
          ggInducedAut θ δ ∈ I) ∨
        ((lab.tag = .F4 ∨ lab.tag = .G2 ∨ lab.tag = .triD4) ∧ ggInducedAut θ δ ∈ I) :=
      largeEvenMarking_mono (fun lab _ _ I _ θ h => by
        simp only [GGTorsionAmbExc] at h
        tauto) hmark
    rcases largeEvenMarking_or hmark' with hE | hL
    · exact hF4 p X hX δ J ⟨hp, hp2, hδp, hδ1, hcomp, hE⟩ h2
    · exact ggTorsionKnownOver_excLowF4 p X hX δ J ⟨hp, hp2, hδp, hδ1, hcomp, hL⟩ h2

end TorsionExc

end CFSG.StandardType
