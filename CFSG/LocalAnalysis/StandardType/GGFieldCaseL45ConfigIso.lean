module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Inn

variable {R R' : Type} [Group R] [Group R']

theorem ggInndiag_eq_range_of_subset {I : Set (MulAut R)} (h : I ⊆ LargeEvenInnSet R) :
    ggInndiag R I = (MulAut.conj : R →* MulAut R).range := by
  refine le_antisymm (sup_le le_rfl ((Subgroup.closure_le _).mpr fun φ hφ => ?_)) le_sup_left
  obtain ⟨r, hr⟩ := h hφ
  exact ⟨r, hr⟩

theorem ggCongr_mem_range_conj_iff (σ : R ≃* R') (φ : MulAut R) :
    MulAut.congr σ φ ∈ (MulAut.conj : R' →* MulAut R').range ↔
      φ ∈ (MulAut.conj : R →* MulAut R).range := by
  constructor
  · rintro ⟨r', hr'⟩
    refine ⟨σ.symm r', ?_⟩
    ext s
    have h := congrArg (fun ψ : MulAut R' => ψ (σ s)) hr'
    simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h
    rw [MulAut.conj_apply]
    apply σ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h
  · rintro ⟨r, rfl⟩
    refine ⟨σ r, ?_⟩
    ext s
    simp [MulAut.conj_apply, MulAut.congr_apply]

theorem ggInndiag_congr_iff_of_subset_inn {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : I ⊆ LargeEvenInnSet R) (hI' : I' ⊆ LargeEvenInnSet R') (σ : R ≃* R') (φ : MulAut R) :
    φ ∈ ggInndiag R I ↔ MulAut.congr σ φ ∈ ggInndiag R' I' := by
  rw [ggInndiag_eq_range_of_subset hI, ggInndiag_eq_range_of_subset hI',
    ggCongr_mem_range_conj_iff]

end Inn

@[expose] def GGRawInndiagIsoOn (S : LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∀ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' → S lab lab' →
        LargeEvenLabelAll lab' (LargeEvenSimpleGuard fun R' _ I' _ =>
          ∀ (σ : R ≃* R') (φ : MulAut R), φ ∈ ggInndiag R I ↔ MulAut.congr σ φ ∈ ggInndiag R' I'))

theorem ggRawInndiagIsoInput_of_on {S S' : LargeEvenLabel → LargeEvenLabel → Prop}
    (h : GGRawInndiagIsoOn S) (h' : GGRawInndiagIsoOn S') (hSS : ∀ lab lab', S lab lab' ∨ S' lab lab') :
    GGRawInndiagIsoInput := by
  intro lab hlab Q hQ
  have h2 := h' lab hlab _ (h lab hlab Q hQ)
  refine largeEvenRawDatum_mono ?_ h2
  rintro R _ I F ⟨⟨hQ, hS⟩, hS'⟩
  refine ⟨hQ, fun hs hna lab' hlab' => ?_⟩
  rcases hSS lab lab' with hl | hl
  · exact hS hs hna lab' hlab' hl
  · exact hS' hs hna lab' hlab' hl

theorem ggRawInndiagIsoOn_inn :
    GGRawInndiagIsoOn fun lab lab' => GGInnerDiagInnLabel lab ∧ GGInnerDiagInnLabel lab' := by
  intro lab hlab Q hQ
  by_cases hinn : GGInnerDiagInnLabel lab
  · refine largeEvenRawDatum_mono ?_ (largeEvenLabelAll_subset_inn hlab hinn Q hQ)
    rintro R _ I F ⟨hQ, hIinn⟩
    refine ⟨hQ, fun hs hna lab' hlab' hl Q' hQ' => ?_⟩
    refine largeEvenRawDatum_mono ?_ (largeEvenLabelAll_subset_inn hlab' hl.2 Q' hQ')
    rintro R' _ I' F' ⟨hQ', hI'inn⟩
    exact ⟨hQ', fun hs' hna' => ggInndiag_congr_iff_of_subset_inn (hIinn hs hna) (hI'inn hs' hna')⟩
  · refine largeEvenRawDatum_mono ?_ hQ
    intro R _ I F hQ
    exact ⟨hQ, fun _ _ lab' _ hl => absurd hl.1 hinn⟩

@[expose] def GGRawInndiagIsoRestInput : Prop :=
  GGRawInndiagIsoOn fun lab lab' => ¬ (GGInnerDiagInnLabel lab ∧ GGInnerDiagInnLabel lab')

theorem ggRawInndiagIsoInput_of_rest
    (h : GGRawInndiagIsoRestInput) : GGRawInndiagIsoInput :=
  ggRawInndiagIsoInput_of_on ggRawInndiagIsoOn_inn h fun _ _ => em _

end CFSG.StandardType

end
