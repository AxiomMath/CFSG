module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly

theorem ggMarkingAll_induces (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {X : Type*} [Group X] {ι : Type*} (rel : ι → X → X → Prop) (S : Set ι)
    (h : ∀ s ∈ S, LargeEvenMarking X fun _ _ _ I _ θ =>
      ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (rel s) φ) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ =>
      ∀ s ∈ S, ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (rel s) φ := by
  intro P hP
  obtain ⟨hX, lab, hlab, hrawP⟩ := hP
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_
    (hraw 3 Nat.prime_three (by norm_num) lab hlab _ (hiso lab hlab _ hrawP))⟩
  rintro R _ I F ⟨⟨⟨hs, hna, θ, hθ⟩, hisoR⟩, hinnR⟩
  obtain ⟨hmul, hinv, hinn, -⟩ := hinnR hs hna
  refine ⟨hs, hna, θ, hθ, fun s hsS => ?_⟩
  obtain ⟨-, labₛ, hlabₛ, hrawₛ⟩ := h s hsS
  obtain ⟨Rₛ, _, Iₛ, Fₛ, ⟨hss, hnas, θₛ, φₛ, hφₛ, hind⟩, hisoₛ⟩ :=
    largeEvenRawDatum_exists (hisoR hs hna labₛ hlabₛ _ hrawₛ)
  have hmem : (MulAut.congr (θ.symm.trans θₛ)).symm φₛ ∈ ggInndiag R I :=
    (hisoₛ hss hnas (θ.symm.trans θₛ) _).2 (by
      rw [MulEquiv.apply_symm_apply]; exact Subgroup.mem_sup_right hφₛ)
  refine ⟨_, Subgroup.subset_closure ((ggL45_mem_ggInndiag_iff hmul hinv hinn).1 hmem), ?_⟩
  intro l l' hl
  simp only [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply, hind l l' hl]

theorem ggMarkingAll_not_induces (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {X : Type*} [Group X] {rel : X → X → Prop}
    (h : LargeEvenMarking X fun _ _ _ I _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ rel φ) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ rel φ := by
  intro P hP
  obtain ⟨hX, lab, hlab, hrawP⟩ := hP
  obtain ⟨-, labₕ, hlabₕ, hrawₕ⟩ := h
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ (hiso lab hlab _ hrawP)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hisoR⟩
  refine ⟨hs, hna, θ, hθ, ?_⟩
  rintro ⟨φ, hφ, hind⟩
  obtain ⟨Rₕ, _, Iₕ, Fₕ, ⟨⟨hsₕ, hnaₕ, θₕ, hnot⟩, hinnₕ⟩, hisoₕ⟩ :=
    largeEvenRawDatum_exists (hisoR hs hna labₕ hlabₕ _
      (hraw 3 Nat.prime_three (by norm_num) labₕ hlabₕ _ hrawₕ))
  obtain ⟨hmul, hinv, hinn, -⟩ := hinnₕ hsₕ hnaₕ
  refine hnot ⟨MulAut.congr (θ.symm.trans θₕ) φ, Subgroup.subset_closure
    ((ggL45_mem_ggInndiag_iff hmul hinv hinn).1
      ((hisoₕ hsₕ hnaₕ (θ.symm.trans θₕ) φ).1 (Subgroup.mem_sup_right hφ))), ?_⟩
  intro l l' hl
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply, hind l l' hl]

end CFSG.StandardType.SCFourCover
