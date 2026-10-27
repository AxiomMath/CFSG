module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Open
open CFSG.SeitzReduction.F4Pilot (evenLieOrder card_eq_evenLieOrder_of_mem_classicalTags)

namespace E6QTwo

theorem card_eq_evenLieOrder_of_hasLabel_twA3 {R : Type} [Group R]
    (h : GGHasLabel ⟨.twA, 3, 1⟩ R) : Nat.card R = evenLieOrder .PSU 4 1 := by
  unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum at h
  simp only [LargeEvenRecipeUnitary] at h
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hKcard
  have hM : LieModel (LargeEvenProj (LargeEvenSUGroup (Fin 4) K 2)) .PSU 4 2 1 :=
    Or.inl ⟨by decide, statedClassicalModel_unitary 4 1 hK' ⟨Nat.prime_two, by norm_num,
      by norm_num, by decide⟩⟩
  rw [Nat.card_congr e.toEquiv]
  exact card_eq_evenLieOrder_of_mem_classicalTags (by decide) hM

private theorem card_eq_evenLieOrder_of_hasLabel_twA4 {R : Type} [Group R]
    (h : GGHasLabel ⟨.twA, 4, 1⟩ R) : Nat.card R = evenLieOrder .PSU 5 1 := by
  unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum at h
  simp only [LargeEvenRecipeUnitary] at h
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hKcard
  have hM : LieModel (LargeEvenProj (LargeEvenSUGroup (Fin 5) K 2)) .PSU 5 2 1 :=
    Or.inl ⟨by decide, statedClassicalModel_unitary 5 1 hK' ⟨Nat.prime_two, by norm_num,
      by norm_num, by decide⟩⟩
  rw [Nat.card_congr e.toEquiv]
  exact card_eq_evenLieOrder_of_mem_classicalTags (by decide) hM

private theorem card_eq_evenLieOrder_of_hasLabel_C4 {R : Type} [Group R]
    (h : GGHasLabel ⟨.C, 4, 1⟩ R) : Nat.card R = evenLieOrder .PSp 4 1 := by
  unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum at h
  simp only [LargeEvenRecipeSymplectic] at h
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hK' : Nat.card K = 2 ^ 1 := by simpa using hKcard
  have hM : LieModel (LargeEvenProj (LargeEvenSpGroup K 4)) .PSp 4 2 1 :=
    Or.inl ⟨by decide, statedClassicalModel_symplectic 4 1 hK' ⟨Nat.prime_two, by norm_num,
      by norm_num, by decide⟩⟩
  rw [Nat.card_congr e.toEquiv]
  exact card_eq_evenLieOrder_of_mem_classicalTags (by decide) hM

private theorem card_eq_evenLieOrder_of_hasLabel_D4 {R : Type} [Group R]
    (h : GGHasLabel ⟨.D, 4, 1⟩ R) : Nat.card R = evenLieOrder .POmegaPlus 4 1 := by
  unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum at h
  simp only [LargeEvenRecipeOmegaPlus] at h
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hK' : Nat.card K = 2 ^ 1 := by simpa using hKcard
  have hM : LieModel (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) .POmegaPlus 4 2 1 :=
    Or.inl ⟨by decide, statedClassicalModel_omegaPlus 4 1 hK' ⟨Nat.prime_two, by norm_num,
      by norm_num⟩⟩
  rw [Nat.card_congr e.toEquiv]
  exact card_eq_evenLieOrder_of_mem_classicalTags (by decide) hM

private theorem card_eq_evenLieOrder_of_hasLabel_D5 {R : Type} [Group R]
    (h : GGHasLabel ⟨.D, 5, 1⟩ R) : Nat.card R = evenLieOrder .POmegaPlus 5 1 := by
  unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum at h
  simp only [LargeEvenRecipeOmegaPlus] at h
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hK' : Nat.card K = 2 ^ 1 := by simpa using hKcard
  have hM : LieModel (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 5))) .POmegaPlus 5 2 1 :=
    Or.inl ⟨by decide, statedClassicalModel_omegaPlus 5 1 hK' ⟨Nat.prime_two, by norm_num,
      by norm_num⟩⟩
  rw [Nat.card_congr e.toEquiv]
  exact card_eq_evenLieOrder_of_mem_classicalTags (by decide) hM

theorem eq_twA_or_twD_of_ggLabelIso_twA3 {lab : LargeEvenLabel}
    (h : GGLabelIso lab ⟨.twA, 3, 1⟩) : lab = ⟨.twA, 3, 1⟩ ∨ lab = ⟨.twD, 3, 1⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem tableP_row_twA3 {X : LargeEvenLabel} (h : GGTablePRow 3 ⟨.twA, 3, 1⟩ X) :
    X = ⟨.twA, 4, 1⟩ ∨ X = ⟨.twA, 5, 1⟩ ∨ X = ⟨.C, 4, 1⟩ ∨ X = ⟨.D, 4, 1⟩ ∨
      X = ⟨.D, 5, 1⟩ := by
  unfold GGTablePRow at h
  norm_num at h
  tauto

private theorem tableP_row_twD3 {X : LargeEvenLabel} (h : GGTablePRow 3 ⟨.twD, 3, 1⟩ X) :
    X = ⟨.D, 4, 1⟩ := by
  unfold GGTablePRow at h
  norm_num at h
  tauto

theorem eq_twA5_of_ggTablePRow {labJ labK : LargeEvenLabel} {R : Type} [Group R]
    (hJ : labJ = ⟨.twA, 3, 1⟩ ∨ labJ = ⟨.twD, 3, 1⟩)
    (hrow : GGTablePRow 3 labJ labK) (hglK : GGHasLabel labK R)
    (h36 : 3 ^ 6 ∣ Nat.card R) : labK = ⟨.twA, 5, 1⟩ := by
  rcases hJ with rfl | rfl
  · rcases tableP_row_twA3 hrow with rfl | rfl | rfl | rfl | rfl
    · exfalso
      rw [card_eq_evenLieOrder_of_hasLabel_twA4 hglK] at h36
      exact absurd h36 (by decide)
    · rfl
    · exfalso
      rw [card_eq_evenLieOrder_of_hasLabel_C4 hglK] at h36
      exact absurd h36 (by decide)
    · exfalso
      rw [card_eq_evenLieOrder_of_hasLabel_D4 hglK] at h36
      exact absurd h36 (by decide)
    · exfalso
      rw [card_eq_evenLieOrder_of_hasLabel_D5 hglK] at h36
      exact absurd h36 (by decide)
  · rw [tableP_row_twD3 hrow] at hglK ⊢
    exfalso
    rw [card_eq_evenLieOrder_of_hasLabel_D4 hglK] at h36
    exact absurd h36 (by decide)

end E6QTwo

end CFSG.StandardType

end
