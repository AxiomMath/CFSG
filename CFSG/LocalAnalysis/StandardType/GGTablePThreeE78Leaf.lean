module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE78Comp
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6NotG2
import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem exists_label_hasLabel_of_marking {J : Type} [Group J] {P : LargeEvenMarkProp J}
    (h : LargeEvenMarking J P) :
    ∃ (lab : LargeEvenLabel) (R : Type) (_ : Group R) (I F : Set (MulAut R))
      (θ : J ⧸ Subgroup.center J ≃* R),
      LargeEvenInLambda2 lab ∧ P lab R I F θ ∧ GGHasLabel lab (J ⧸ Subgroup.center J) := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, _, θ, hP⟩ := hQ
  refine ⟨lab, R, hR, I, F, θ, hlab, hP, ?_⟩
  refine largeEvenRawDatum_mono (fun R _ I F h => ?_) hraw
  obtain ⟨-, -, θ', -⟩ := h
  exact ⟨θ'⟩

private theorem datumOn_mono {F F' : LargeEvenLieTag → Prop}
    (hFF : ∀ t, F t → F' t) {X : Type} [Group X]
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (h : DatumOn F X A δ J) : DatumOn F' X A δ J :=
  ⟨h.1, h.2.1, h.2.2.1,
    largeEvenMarking_mono
      (fun lab R _ I F'' θ ⟨hF, hs3, hin⟩ => ⟨hFF lab.tag hF, hs3, hin⟩) h.2.2.2⟩

private theorem e78_not_small {lab : LargeEvenLabel} (h : E78CompLabel lab) :
    ¬ (lab.rank ≤ 2 ∧ (lab.tag = .A ∨ lab.tag = .twA)) ∧
      lab.tag ≠ .triD4 ∧ ¬ (lab.tag = .D ∧ lab.rank = 4) := by
  unfold E78CompLabel at h
  rcases h with ⟨ht, hr⟩ | ⟨ht, hr⟩ | hE | hE | hE | hE
  · refine ⟨?_, ?_, ?_⟩
    · rintro ⟨hh1, -⟩
      omega
    · rintro hh
      rcases ht with h' | h' <;> rw [h'] at hh <;> exact absurd hh (by decide)
    · rintro ⟨hD, -⟩
      rcases ht with h' | h' <;> rw [h'] at hD <;> exact absurd hD (by decide)
  · refine ⟨?_, ?_, ?_⟩
    · rintro ⟨hh1, -⟩
      omega
    · rintro hh
      rcases ht with h' | h' <;> rw [h'] at hh <;> exact absurd hh (by decide)
    · rintro ⟨-, hr4⟩
      omega
  · exact ⟨fun hh => by rcases hh.2 with h' | h' <;> exact absurd (hE.symm.trans h') (by decide),
      fun hh => absurd (hE.symm.trans hh) (by decide),
      fun hh => absurd (hE.symm.trans hh.1) (by decide)⟩
  · exact ⟨fun hh => by rcases hh.2 with h' | h' <;> exact absurd (hE.symm.trans h') (by decide),
      fun hh => absurd (hE.symm.trans hh) (by decide),
      fun hh => absurd (hE.symm.trans hh.1) (by decide)⟩
  · exact ⟨fun hh => by rcases hh.2 with h' | h' <;> exact absurd (hE.symm.trans h') (by decide),
      fun hh => absurd (hE.symm.trans hh) (by decide),
      fun hh => absurd (hE.symm.trans hh.1) (by decide)⟩
  · exact ⟨fun hh => by rcases hh.2 with h' | h' <;> exact absurd (hE.symm.trans h') (by decide),
      fun hh => absurd (hE.symm.trans hh) (by decide),
      fun hh => absurd (hE.symm.trans hh.1) (by decide)⟩

private theorem not_small_of_e78_of_ggLabelIso {lab lab' : LargeEvenLabel}
    (hLab : E78CompLabel lab) (hIso : GGLabelIso lab lab') :
    ¬ (lab'.rank ≤ 2 ∧ (lab'.tag = .A ∨ lab'.tag = .twA)) ∧
      lab'.tag ≠ .triD4 ∧ ¬ (lab'.tag = .D ∧ lab'.rank = 4) := by
  rcases hIso with h | h | h | h | h | h | h | h
  · rw [← h]
    exact e78_not_small hLab
  · exfalso
    obtain ⟨hb, -⟩ := h
    unfold E78CompLabel at hLab
    rcases hLab with ⟨ht, -⟩ | ⟨ht, -⟩ | hE | hE | hE | hE
    · rcases ht with ht | ht <;> rcases hb with hb | hb <;>
        exact absurd (hb.symm.trans ht) (by decide)
    · rcases ht with ht | ht <;> rcases hb with hb | hb <;>
        exact absurd (hb.symm.trans ht) (by decide)
    · rcases hb with hb | hb <;> exact absurd (hb.symm.trans hE) (by decide)
    · rcases hb with hb | hb <;> exact absurd (hb.symm.trans hE) (by decide)
    · rcases hb with hb | hb <;> exact absurd (hb.symm.trans hE) (by decide)
    · rcases hb with hb | hb <;> exact absurd (hb.symm.trans hE) (by decide)
  · obtain ⟨-, h2⟩ := h
    rw [h2]
    dsimp only
    decide
  · obtain ⟨-, h2⟩ := h
    rw [h2]
    dsimp only
    decide
  · obtain ⟨-, h2⟩ := h
    rw [h2]
    dsimp only
    decide
  · obtain ⟨-, h2⟩ := h
    rw [h2]
    dsimp only
    decide
  · exfalso
    obtain ⟨h1, -⟩ := h
    rw [h1] at hLab
    unfold E78CompLabel at hLab
    dsimp only at hLab
    exact absurd hLab (by decide)
  · exfalso
    obtain ⟨-, h2⟩ := h
    rw [h2] at hLab
    unfold E78CompLabel at hLab
    dsimp only at hLab
    exact absurd hLab (by decide)

private theorem e78_six_of_tag
    {F : LargeEvenLieTag → Prop} (hF : ∀ t, F t → t = .E7 ∨ t = .E8) :
    KnownOverSix (DatumOn F) := by
  have compLabel : ∀ {X : Type} [Group X] [Finite X]
      {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X},
      DatumOn F X A δ J →
      ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ E78CompLabel lab ∧
        GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := by
    intro X _ _ A δ J hd
    obtain ⟨hK, huniq, _hcard, hmark⟩ := hd
    obtain ⟨haut, _hker⟩ := hK
    obtain ⟨hAe, hδA, hδ1, hcomp, _hnorm⟩ := haut
    have hdat : GGTorsionDatum (fun lab : LargeEvenLabel => lab.tag = .E7 ∨ lab.tag = .E8)
        3 δ J := by
      refine ⟨Nat.prime_three, by norm_num, ?_, hδ1, hcomp, ?_⟩
      · exact hAe.2 δ hδA
      · refine largeEvenMarking_mono ?_ hmark
        rintro lab R _ I F' θ ⟨hFtag, _hspl, hinn⟩
        exact ⟨hF lab.tag hFtag, hinn δ hδA⟩
    have hcomp78 := ggTorsion_e78_comp hdat
    unfold GGCompE78 at hcomp78
    rcases hcomp78 with ⟨J', hJ', hJ'ne⟩ | ⟨lab, hlab, hHas, hLab⟩
    · exact absurd (huniq J' hJ') hJ'ne
    · exact ⟨lab, hlab, hLab, hHas⟩
  unfold KnownOverSix
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ hX A δ J hd
    exact kg5a_exc hX (datumOn_mono (fun t ht => Or.inr (Or.inr (hF t ht))) hd)
  · intro X _ _ hX A δ J hd hmarkA2 _hZ _hAll
    obtain ⟨lab, hlab, hLab, hHas⟩ := compLabel hd
    obtain ⟨lab', R, hR, I, F', θ, hlab', hP, hHas'⟩ :=
      exists_label_hasLabel_of_marking hmarkA2
    have hIso := ggLabelRigidInput_holds lab lab' (↥J ⧸ Subgroup.center ↥J) hlab hlab' hHas hHas'
    obtain ⟨hsmall, -, -⟩ := not_small_of_e78_of_ggLabelIso hLab hIso
    exact absurd ⟨le_of_eq hP.1, hP.2.2.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩ hsmall
  · intro X _ _ hX A δ J hd hmarkA2tw _hZ _hAll
    obtain ⟨lab, hlab, hLab, hHas⟩ := compLabel hd
    obtain ⟨lab', R, hR, I, F', θ, hlab', hP, hHas'⟩ :=
      exists_label_hasLabel_of_marking hmarkA2tw
    have hIso := ggLabelRigidInput_holds lab lab' (↥J ⧸ Subgroup.center ↥J) hlab hlab' hHas hHas'
    obtain ⟨hsmall, -, -⟩ := not_small_of_e78_of_ggLabelIso hLab hIso
    have hA2 : GGLabelA2 lab' := hP.1
    exact absurd ⟨le_of_eq hA2.1, hA2.2.2.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩ hsmall
  · intro X _ _ hX A δ J hd hmarkTri _hAll
    obtain ⟨lab, hlab, hLab, hHas⟩ := compLabel hd
    obtain ⟨lab', R, hR, I, F', θ, hlab', hP, hHas'⟩ :=
      exists_label_hasLabel_of_marking hmarkTri
    have hIso := ggLabelRigidInput_holds lab lab' (↥J ⧸ Subgroup.center ↥J) hlab hlab' hHas hHas'
    obtain ⟨-, htri, -⟩ := not_small_of_e78_of_ggLabelIso hLab hIso
    exact absurd hP htri
  · intro X _ _ hX A δ J hd hmarkD _hAll
    obtain ⟨lab, hlab, hLab, hHas⟩ := compLabel hd
    obtain ⟨lab', R, hR, I, F', θ, hlab', hP, hHas'⟩ :=
      exists_label_hasLabel_of_marking hmarkD
    have hIso := ggLabelRigidInput_holds lab lab' (↥J ⧸ Subgroup.center ↥J) hlab hlab' hHas hHas'
    obtain ⟨-, -, hD4⟩ := not_small_of_e78_of_ggLabelIso hLab hIso
    exact absurd ⟨hP.1, hP.2.1⟩ hD4
  · intro X _ _ hX A δ J hd hmarkA1
    obtain ⟨lab, hlab, hLab, hHas⟩ := compLabel hd
    obtain ⟨lab', R, hR, I, F', θ, hlab', hP, hHas'⟩ :=
      exists_label_hasLabel_of_marking hmarkA1
    have hIso := ggLabelRigidInput_holds lab lab' (↥J ⧸ Subgroup.center ↥J) hlab hlab' hHas hHas'
    obtain ⟨hsmall, -, -⟩ := not_small_of_e78_of_ggLabelIso hLab hIso
    exact absurd ⟨by omega, Or.inl hP.1⟩ hsmall

theorem leafE78Six_holds
    (i : Fin 11) (hi : i = 8 ∨ i = 9) : KnownOverSix (DatumOn (fam i)) := by
  rcases hi with rfl | rfl
  · exact e78_six_of_tag (F := fam 8) (fun t ht => Or.inl (by simpa only [fam] using ht))
  · exact e78_six_of_tag (F := fam 9) (fun t ht => Or.inr (by simpa only [fam] using ht))

end CFSG.StandardType.TablePThreeKG

end
