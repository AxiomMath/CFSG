module

public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallBIsoLinear
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallBIsoUnitary
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

section Symplectic

open RecipeFieldSp

theorem ggInndiagCommEq_symplectic {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hm : 3 ≤ m) :
    GGInndiagCommEq (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) :=
  ggInndiag_eq_comm_of_subset_inn (fun _ hφ => mem_conjImage_iff_inn.mp hφ)
    (commutator_mem_inn_symplectic hm)

theorem largeEvenLabelAll_inndiagComm_symplectic {lab : LargeEvenLabel}
    (h : GGSymplecticHighLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  intro Q₀ hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hS, hl3⟩ := h
  dsimp only at hl3
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) hQ
    have : CharP K 2 := charP_two_of_card hK
    exact fun _ _ => ggInndiagCommEq_symplectic hl3
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) hQ
    have : CharP K 2 := charP_two_of_card hK
    exact fun _ _ => ggInndiagCommEq_symplectic hl3

end Symplectic

@[expose] def GGInndiagCommExclLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .B2der

@[expose] def GGInndiagCommProvedLabel (lab : LargeEvenLabel) : Prop :=
  GGInndiagCommLinearLabel lab ∨ GGInndiagUnitaryLabel lab ∨ GGRecipeExcOutLabel lab ∨
    GGSymplecticHighLabel lab


theorem largeEvenLabelAll_inndiagComm_proved {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGInndiagCommProvedLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  rcases h with h | h | h | h
  · exact largeEvenLabelAll_inndiagComm_linear h
  · exact largeEvenLabelAll_inndiagComm_unitary hlab h
  · exact largeEvenLabelAll_inndiagComm_excOut hlab h
  · exact largeEvenLabelAll_inndiagComm_symplectic h

@[expose] def GGInndiagCommRestInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → ¬ GGInndiagCommExclLabel lab →
    ¬ GGInndiagCommProvedLabel lab → LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq)

@[expose] def GGRawInndiagIsoExclInput : Prop :=
  GGRawInndiagIsoOn fun lab lab' => ¬ (GGInnerDiagInnLabel lab ∧ GGInnerDiagInnLabel lab') ∧
    (GGInndiagCommExclLabel lab ∨ GGInndiagCommExclLabel lab')

theorem ggRawInndiagIsoRestInput_of_comm (hC : GGInndiagCommRestInput)
    (hX : GGRawInndiagIsoExclInput) : GGRawInndiagIsoRestInput := by
  refine ggRawInndiagIsoOn_of_or
    (ggRawInndiagIsoOn_of_comm (S := fun lab => ¬ GGInndiagCommExclLabel lab) ?_) hX ?_
  · intro lab hlab hS
    by_cases hP : GGInndiagCommProvedLabel lab
    · exact largeEvenLabelAll_inndiagComm_proved hlab hP
    · exact hC lab hlab hS hP
  · intro lab lab' hl
    by_cases h1 : GGInndiagCommExclLabel lab
    · exact Or.inr ⟨hl, Or.inl h1⟩
    by_cases h2 : GGInndiagCommExclLabel lab'
    · exact Or.inr ⟨hl, Or.inr h2⟩
    exact Or.inl ⟨h1, h2⟩

end CFSG.StandardType

end
