module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeF4Comp
import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem inLambda2_C_three {n : ℕ} (hn : 1 ≤ n) : LargeEvenInLambda2 ⟨.C, 3, n⟩ := by
  unfold LargeEvenInLambda2
  refine ⟨hn, by norm_num, ?_⟩
  intro h
  norm_num at h

private theorem tag_rank_of_ggLabelIso_C3 {lab : LargeEvenLabel} {n : ℕ}
    (h : GGLabelIso lab ⟨.C, 3, n⟩) : (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 := by
  rcases h with h | h | h | h | h | h | h | h
  · rw [h]; exact ⟨Or.inr rfl, rfl⟩
  · exact ⟨h.1, h.2.2.1⟩
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by simp)

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

section F4LeafCerts

private theorem f4_cell_label_BC
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 7) X A δ J) {P : LargeEvenMarkProp J} (hmarkJ : LargeEvenMarking J P) :
    ∃ (lab : LargeEvenLabel) (R : Type) (_ : Group R) (I F : Set (MulAut R))
      (θ : J ⧸ Subgroup.center J ≃* R),
      LargeEvenInLambda2 lab ∧ P lab R I F θ ∧
        (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 := by
  unfold DatumOn at hd
  dsimp only [fam] at hd
  obtain ⟨hK, huniq, _hcard, hmarkX⟩ := hd
  obtain ⟨haut, _hker⟩ := hK
  obtain ⟨hAe, hδA, hδ1, hcomp, _hnorm⟩ := haut
  have hdat : GGTorsionDatum (fun lab : LargeEvenLabel => lab.tag = .F4) 3 δ J := by
    refine ⟨Nat.prime_three, by norm_num, ?_, hδ1, hcomp, ?_⟩
    · exact hAe.2 δ hδA
    · refine largeEvenMarking_mono ?_ hmarkX
      rintro lab R _ I F θ ⟨htag, -, hinn⟩
      exact ⟨htag, hinn δ hδA⟩
  have hF4 := ggTorsion_f4_comp hdat
  obtain ⟨-, labX, hlabX, hrawX⟩ := hF4
  obtain ⟨_, _, _, _, hQX⟩ := largeEvenRawDatum_exists hrawX
  obtain ⟨-, _, _θX, hPX⟩ := hQX
  obtain ⟨-, hcompX⟩ := hPX
  rcases hcompX with ⟨J', hJ'comp, hJ'ne⟩ | hC3
  · exact absurd (huniq J' hJ'comp) hJ'ne
  · have hlamC := inLambda2_C_three hlabX.1
    obtain ⟨lab, R, hR, I, F, θ, hlab, hP, hHas⟩ := exists_label_hasLabel_of_marking hmarkJ
    have hIso := ggLabelRigidInput_holds lab ⟨.C, 3, labX.n⟩ (↥J ⧸ Subgroup.center ↥J)
      hlab hlamC hHas hC3
    exact ⟨lab, R, hR, I, F, θ, hlab, hP, tag_rank_of_ggLabelIso_C3 hIso⟩

end F4LeafCerts

theorem leafF4Six_holds :
    KnownOverSix (DatumOn (fam 7)) := by
  unfold KnownOverSix
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ hX A δ J hd hmarkG2
    obtain ⟨lab, _, _, _, _, _, hlab, hG2, hbc, _hr3⟩ := f4_cell_label_BC hd hmarkG2
    rcases hbc with hB | hC
    · rcases hG2 with h2 | h2 <;> exact absurd (hB.symm.trans h2) (by decide)
    · rcases hG2 with h2 | h2 <;> exact absurd (hC.symm.trans h2) (by decide)
  · intro X _ _ hX A δ J hd hmarkA2 _hZ _hAll
    obtain ⟨lab, _, _, _, _, _, _hlab, hA2, _hbc, hr3⟩ := f4_cell_label_BC hd hmarkA2
    have hrank : lab.rank = 2 := hA2.1
    exact (by omega : False).elim
  · intro X _ _ hX A δ J hd hmarkA2 _hZ _hAll
    obtain ⟨lab, _, _, _, _, _, _hlab, hA2, _hbc, hr3⟩ := f4_cell_label_BC hd hmarkA2
    have hrank : lab.rank = 2 := hA2.1.1
    exact (by omega : False).elim
  · intro X _ _ hX A δ J hd htriD4
    obtain ⟨lab, _, _, _, _, _, _hlab, hP, hbc, _hr3⟩ := f4_cell_label_BC hd htriD4
    rcases hbc with hB | hC
    · exact absurd (hB.symm.trans hP) (by decide)
    · exact absurd (hC.symm.trans hP) (by decide)
  · intro X _ _ hX A δ J hd hmarkD
    obtain ⟨lab, _, _, _, _, _, _hlab, hP, _hbc, hr3⟩ := f4_cell_label_BC hd hmarkD
    have hrank : lab.rank = 4 := hP.2.1
    exact (by omega : False).elim
  · intro X _ _ hX A δ J hd hmarkA1
    obtain ⟨lab, _, _, _, _, _, _hlab, hP, _hbc, hr3⟩ := f4_cell_label_BC hd hmarkA1
    have hrank : lab.rank = 1 := hP.2
    exact (by omega : False).elim

end CFSG.StandardType.TablePThreeKG

end
