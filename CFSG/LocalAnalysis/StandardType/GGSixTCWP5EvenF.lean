module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrame
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Open CFSG.StandardType

section EvenF

theorem false_of_fieldExt_label_A1_twE6
    {X : Type} [Group X] {J : Subgroup X} (hJ : CFSG.Open.IsQuasisimple ↥J) {f : ℕ} (hf : 1 ≤ f)
    (hlab : GGHasLabel ⟨.A, 1, 2 * f⟩ (↥J ⧸ Subgroup.center ↥J))
    (hF : GGSixLSevenFieldExtCase J .twistedE6 f) : False := by
  obtain ⟨t', m, f', -, hmod, hnot⟩ := hF
  have hcen : Subgroup.center (↥J ⧸ Subgroup.center ↥J) = ⊥ :=
    center_quot_eq_bot_of_isQuasisimple hJ
  obtain ⟨lab', hlab', ht', -, -, hdeg', hraw'⟩ := exists_label_rawDatum_of_lieModel hcen hmod
  have hΛ : LargeEvenInLambda2 (⟨.A, 1, 2 * f⟩ : LargeEvenLabel) :=
    ⟨by simp; omega, by simp, fun _ => by simp; omega⟩
  have hiso := ggLabelRigidInput_holds _ lab' (↥J ⧸ Subgroup.center ↥J) hΛ hlab' hlab hraw'
  apply hnot
  obtain ⟨tg, r, n⟩ := lab'
  rcases hiso with h | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, h2⟩
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨ht'.symm, hdeg'.symm, Or.inr rfl⟩
  · simp at h1
  · simp at h1
  · simp at h1
  · simp at h1
  · simp at h1
  · simp at h1
  · simp only [LargeEvenLabel.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl, -⟩ := h1
    refine ⟨?_, ?_, Or.inr rfl⟩
    · rw [← ht']
      simp [markTag]
    · rw [← hdeg']
      simp only [markDeg, if_true]
      omega

end EvenF

end CFSG.StandardType.TableCRes

end
