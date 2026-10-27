module

public import CFSG.LocalAnalysis.StandardType.GGTorsionTwF4Card
import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionClassical

theorem ggTorsion_not_marking_of_classical
    {J : Type} [Group J]
    (h : (∃ (t : CFSG.Open.StatedLieTag) (n f : ℕ),
        CFSG.Open.StatedClassicalModel (J ⧸ Subgroup.center J) t n 2 f) ∨
      Nat.card (J ⧸ Subgroup.center J) = 360) :
    ¬ LargeEvenMarking J fun lab _ _ _ _ _ => GGL45TorsionTag lab := by
  intro hmark
  obtain ⟨-, labJ, hlabJ, hrawJ⟩ := largeEvenMarking_markedModel hmark
  obtain ⟨R, _, I, F, _hs, _hna, θ, hP, hM⟩ := largeEvenRawDatum_exists hrawJ
  have hP' : labJ.tag = .E8 ∨ labJ.tag = .F4 ∨ labJ.tag = .twF4 ∨ labJ.tag = .twF4der := by
    simpa only [GGL45TorsionTag] using hP
  rcases h with ⟨t, n, f, hL⟩ | h360
  · obtain ⟨lab, hlab, htag, -, -, -, hraw⟩ :=
      CFSG.StandardType.exists_label_rawDatum_of_statedClassicalModel hL
    have hasJ : GGHasLabel labJ (J ⧸ Subgroup.center J) := by
      refine largeEvenRawDatum_mono ?_ hrawJ
      intro R _ I F h
      obtain ⟨-, -, θ, -⟩ := h
      exact ⟨θ⟩
    have hIso : GGLabelIso labJ lab :=
      ggLabelRigidInput_holds labJ lab (J ⧸ Subgroup.center J) hlabJ hlab hasJ hraw
    have hEq : labJ = lab := eq_of_ggLabelIso_of_torsionTag hIso hP
    subst hEq
    obtain ⟨tg, l, n'⟩ := labJ
    rcases hP' with rfl | rfl | rfl | rfl <;> dsimp only [markTag] at htag <;> subst htag <;>
      exact hL.2.elim
  · have hcard : Nat.card R = 360 := by
      rw [← h360]
      exact (Nat.card_congr θ.toEquiv).symm
    have hne : labJ.tag ≠ .B2der := by
      rcases hP' with h | h | h | h <;> rw [h] <;> decide
    exact ggMarkedModel_card_ne_three_sixty hne hM hcard

end TorsionClassical

end CFSG.StandardType
