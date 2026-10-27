module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpULie

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

private lemma spUCited_conjSubgroup_map {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    (K : Subgroup L) (g : L) :
    conjSubgroup (K.map φ.toMonoidHom) (φ g) = (conjSubgroup K g).map φ.toMonoidHom := by
  have hhom : (MulAut.conj ((φ g)⁻¹)).toMonoidHom.comp φ.toMonoidHom
      = φ.toMonoidHom.comp (MulAut.conj (g⁻¹)).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply]
  unfold conjSubgroup
  simp only [Subgroup.map_map]
  rw [hhom]

private lemma spUCited_map_map_congr {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    (α : MulAut L) (K : Subgroup L) :
    (K.map φ.toMonoidHom).map (MulAut.congr φ α).toMonoidHom
      = (K.map α.toMonoidHom).map φ.toMonoidHom := by
  have hhom : (MulAut.congr φ α).toMonoidHom.comp φ.toMonoidHom
      = φ.toMonoidHom.comp α.toMonoidHom := by
    ext y
    simp [MulAut.congr]
  simp only [Subgroup.map_map]
  rw [hhom]

private lemma spUCited_map_inf_normalizer {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    (H X : Subgroup L) :
    (H ⊓ Subgroup.normalizer (X : Set L)).map φ.toMonoidHom
      = H.map φ.toMonoidHom
        ⊓ Subgroup.normalizer ((X.map φ.toMonoidHom : Subgroup L') : Set L') := by
  rw [Subgroup.map_inf H (Subgroup.normalizer (X : Set L)) φ.toMonoidHom φ.injective,
    Subgroup.map_equiv_normalizer_eq]

theorem rootParabolic_of_mulEquiv {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    {R Sy X₂ Pα : Subgroup L} {e : ℕ}
    (h : RootParabolic (R.map φ.toMonoidHom) (Sy.map φ.toMonoidHom) (X₂.map φ.toMonoidHom)
      (Pα.map φ.toMonoidHom) e) :
    RootParabolic R Sy X₂ Pα e := by
  have hle_src : Sy ≤ Pα :=
    (Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective).mp h.le
  refine
    { mem := ?_
      index := ?_
      one_le := h.one_le
      le := hle_src
      isPGroup := ?_
      normal := ?_
      largest := ?_
      not_le := ?_
      maximal := ?_
      invariant := ?_ }
  · have hmem := h.mem
    simp only [rootGroupsIn, Set.mem_setOf_eq] at hmem
    obtain ⟨⟨g', hg'⟩, hle'⟩ := hmem
    refine ⟨⟨φ.symm g', ?_⟩, ?_⟩
    · apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      rw [← spUCited_conjSubgroup_map φ R (φ.symm g'), φ.apply_symm_apply, hg']
    · exact (Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective).mp hle'
  · have hrel : (Subgroup.normalizer ((X₂.map φ.toMonoidHom : Subgroup L') : Set L')).relIndex
          (Sy.map φ.toMonoidHom)
        = (Subgroup.normalizer (X₂ : Set L)).relIndex Sy := by
      rw [← Subgroup.map_equiv_normalizer_eq X₂ φ]
      exact Subgroup.relIndex_map_map_of_injective (Subgroup.normalizer (X₂ : Set L)) Sy
        φ.injective
    have hcard : Nat.card (R.map φ.toMonoidHom) = Nat.card R :=
      Subgroup.card_map_of_injective φ.injective
    have hi := h.index
    rw [hrel, hcard] at hi
    exact hi
  · have hi := h.isPGroup
    rw [← spUCited_map_inf_normalizer φ Sy X₂] at hi
    exact hi.of_equiv (φ.subgroupMap (Sy ⊓ Subgroup.normalizer (X₂ : Set L))).symm
  · have hle_inf : Sy ⊓ Subgroup.normalizer (X₂ : Set L) ≤ Pα := inf_le_left.trans hle_src
    have hle_inf' : Sy.map φ.toMonoidHom
        ⊓ Subgroup.normalizer ((X₂.map φ.toMonoidHom : Subgroup L') : Set L')
        ≤ Pα.map φ.toMonoidHom := by
      rw [← spUCited_map_inf_normalizer φ Sy X₂]
      exact Subgroup.map_mono hle_inf
    have hN' := (Subgroup.normal_subgroupOf_iff_le_normalizer hle_inf').mp h.normal
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle_inf).mpr ?_
    rw [← Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective]
    rw [Subgroup.map_equiv_normalizer_eq, spUCited_map_inf_normalizer]
    exact hN'
  · intro N hNP hNnorm hNpg
    have hNnorm' : ((N.map φ.toMonoidHom).subgroupOf (Pα.map φ.toMonoidHom)).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hNP)).mpr ?_
      rw [← Subgroup.map_equiv_normalizer_eq N φ]
      exact Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mp hNnorm)
    have hlargest := h.largest (N.map φ.toMonoidHom) (Subgroup.map_mono hNP) hNnorm'
      (hNpg.map φ.toMonoidHom)
    rw [← Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective]
    rw [spUCited_map_inf_normalizer φ Sy X₂]
    exact hlargest
  · intro hle
    apply h.not_le
    rw [← Subgroup.map_equiv_normalizer_eq R φ]
    exact Subgroup.map_mono hle
  · intro M hM
    have hM' : Subgroup.normalizer ((R.map φ.toMonoidHom : Subgroup L') : Set L')
        ≤ M.map φ.toMonoidHom := by
      rw [← Subgroup.map_equiv_normalizer_eq R φ]
      exact Subgroup.map_mono hM
    rcases h.maximal (M.map φ.toMonoidHom) hM' with hcase | hcase
    · left
      apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      rw [hcase, Subgroup.map_equiv_normalizer_eq]
    · right
      apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      rw [hcase, Subgroup.map_top_of_surjective _ φ.surjective]
  · intro α hSy hR
    have hSy' : Subgroup.map (MulAut.congr φ α).toMonoidHom (Subgroup.map φ.toMonoidHom Sy)
        = Subgroup.map φ.toMonoidHom Sy := by
      rw [spUCited_map_map_congr, hSy]
    have hR' : Subgroup.map (MulAut.congr φ α).toMonoidHom (Subgroup.map φ.toMonoidHom R)
        = Subgroup.map φ.toMonoidHom R := by
      rw [spUCited_map_map_congr, hR]
    have hP' := h.invariant (MulAut.congr φ α) hSy' hR'
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [← spUCited_map_map_congr φ α Pα]
    exact hP'

theorem rootParabolic_exists_of_mulEquiv {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    {R Sy : Subgroup L} {e : ℕ}
    (h : ∃ X₂' Pα' : Subgroup L',
      RootParabolic (R.map φ.toMonoidHom) (Sy.map φ.toMonoidHom) X₂' Pα' e) :
    ∃ X₂ Pα : Subgroup L, RootParabolic R Sy X₂ Pα e := by
  obtain ⟨X₂', Pα', hP⟩ := h
  have hm : ∀ H : Subgroup L', (H.map φ.symm.toMonoidHom).map φ.toMonoidHom = H := by
    intro H
    rw [Subgroup.map_map]
    have h1 : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id L' := by
      ext x
      simp
    rw [h1, Subgroup.map_id]
  refine ⟨X₂'.map φ.symm.toMonoidHom, Pα'.map φ.symm.toMonoidHom, rootParabolic_of_mulEquiv φ ?_⟩
  rw [hm, hm]
  exact hP

end CFSG.LocalAnalysis.WeakClosure81

end
