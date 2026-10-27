module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.M22MovingSection
public import CFSG.Quasithin.Background.ConjugateSectionAction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem isSpor_map_conj {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {φ : MulAut W} (h : IsSpor H .M22) :
    IsSpor (H.map (MulAut.conj φ).toMonoidHom) .M22 := by
  obtain ⟨e⟩ := h
  exact ⟨(Subgroup.equivMapOfInjective H (MulAut.conj φ).toMonoidHom
    (MulAut.conj φ).injective).symm.trans e⟩

theorem exists_m22_active_conjugate
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hM22 : IsSpor (lBar V₀ V hV L) .M22)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (hdim : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 10) :
    ∃ t ∈ Mbar D.M V₀ V hV,
      t ^ 2 = 1 ∧ t ≠ 1 ∧
        rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (Subgroup.zpowers t)) ≤ 3 ∧
        ∃ φ ∈ Mbar D.M V₀ V hV,
          let H0 := (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom
          t ∈ Subgroup.normalizer (H0 : Set (MulAut (Vtil V₀ V hV))) ∧
          (¬ ∃ h0 ∈ H0, ∀ h ∈ H0, t * h * t⁻¹ = h0 * h * h0⁻¹) ∧
          ∀ ψ ∈ Mbar D.M V₀ V hV,
            let Hj := (lBar V₀ V hV L).map (MulAut.conj ψ).toMonoidHom
            Hj ≠ H0 →
              t ∈ Subgroup.centralizer (Hj : Set (MulAut (Vtil V₀ V hV))) := by
  classical
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  have hW : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hM22H : IsSpor H .M22 := by simpa [H] using hM22
  have hirrH : commSub (⊤ : Subgroup W) H ∈ irrSet H := by simpa [H, W] using hirr
  have hdimH : E3.mQuot (commSub (⊤ : Subgroup W) H)
      (commSub (⊤ : Subgroup W) H ⊓ fixV H) = 10 := by
    simpa [H, W] using hdim
  obtain ⟨t, htA, ht2, htne, hrk, hc⟩ := c.conc
  have htAW : t ∈ A := by simpa [A] using htA
  have hrkW : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3 := by
    simpa [W] using hrk
  have hspan : (⨆ X ∈ conjSubs A (commSub (⊤ : Subgroup W) H), X) = ⊤ := by
    simpa [A, H, W] using hc.1
  have hcross : ∀ g ∈ A, g ∉ Subgroup.normalizer (H : Set (MulAut W)) →
      commSub (commSub (⊤ : Subgroup W) H) (H.map (MulAut.conj g).toMonoidHom) = ⊥ := by
    intro g hg hgn
    exact (hc.2.1 g (by simpa [A] using hg) (by simpa [H] using hgn)).2
  have hnorm : ∀ a ∈ A, t ∈ Subgroup.normalizer
      (H.map (MulAut.conj a).toMonoidHom : Set (MulAut W)) := by
    intro a ha
    by_contra hnot
    have hle := ConjugateSection.mQuot_le_rk_of_not_mem_normalizer
      (W := W) hcross ha htAW ht2 hnot
    have hdimA : E3.mQuot (commSub (⊤ : Subgroup W) (H.map (MulAut.conj a).toMonoidHom))
        (commSub (⊤ : Subgroup W) (H.map (MulAut.conj a).toMonoidHom) ⊓
          fixV (H.map (MulAut.conj a).toMonoidHom)) = 10 := by
      rw [ConjugateSection.mQuot_commSub_top_inf_fixV_map_conj]
      exact hdimH
    omega
  have hspan' : (⨆ X : {X // X ∈ conjSubs A (commSub (⊤ : Subgroup W) H)},
      (X : Subgroup W)) = ⊤ := by
    simpa only [iSup_subtype'] using hspan
  obtain ⟨X, u, hu, htu⟩ := ConjugateSection.exists_not_fixed_of_iSup_eq_top
    (W := W) hspan' htne
  obtain ⟨φ, hφA, hXeq⟩ := X.2
  have htU0 : ∃ u ∈ commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom),
      t u ≠ u := by
    refine ⟨u, ?_, htu⟩
    rw [hXeq] at hu
    rwa [← s15_Infra_commSub_top_map_conj H φ] at hu
  have hH0spor : IsSpor (H.map (MulAut.conj φ).toMonoidHom) .M22 :=
    isSpor_map_conj hM22H
  have hirr0 : commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) ∈
      irrSet (H.map (MulAut.conj φ).toMonoidHom) := by
    have h := ConjugateSection.map_mem_irrSet_map_conj (H := H) (φ := φ) hirrH
    rwa [← s15_Infra_commSub_top_map_conj H φ] at h
  have hdim0 : E3.mQuot (commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom))
      (commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) ⊓
        fixV (H.map (MulAut.conj φ).toMonoidHom)) = 10 := by
    rw [ConjugateSection.mQuot_commSub_top_inf_fixV_map_conj]
    exact hdimH
  have hrk0 : rk ↥(commSub (commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom))
      (Subgroup.zpowers t)) ≤ 3 :=
    le_trans (rk_mono (commSub_mono le_top le_rfl)) hrkW
  obtain ⟨hq0, houter0⟩ := m22_section_mQuot_eq_three_and_not_inner
    (W := W) (H := H.map (MulAut.conj φ).toMonoidHom) (t := t)
    hW hH0spor hirr0 hdim0 (hnorm φ hφA) ht2 htU0 hrk0
  have hcent : ∀ ψ ∈ A, ∀ (_ : H.map (MulAut.conj ψ).toMonoidHom ≠
      H.map (MulAut.conj φ).toMonoidHom),
        t ∈ Subgroup.centralizer
          (H.map (MulAut.conj ψ).toMonoidHom : Set (MulAut W)) := by
    intro ψ hψA hne
    have hpair := ConjugateSection.commSub_le_fixV_of_conj_ne (W := W) (A := A) (H := H)
      hcross hφA hψA hne.symm
    obtain ⟨hU0fix, hUψfix⟩ := hpair
    have hstab0 : t ∈ stabSub
        (commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom)) := by
      have h := FixVLat.mem_stabSub_commV_of_mem_normalizer
        (X := H.map (MulAut.conj φ).toMonoidHom) (hnorm φ hφA)
      rwa [commV_eq_commSub] at h
    have hstabψ : t ∈ stabSub
        (commSub (⊤ : Subgroup W) (H.map (MulAut.conj ψ).toMonoidHom)) := by
      have h := FixVLat.mem_stabSub_commV_of_mem_normalizer
        (X := H.map (MulAut.conj ψ).toMonoidHom) (hnorm ψ hψA)
      rwa [commV_eq_commSub] at h
    have hint : commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) ⊓
        commSub (⊤ : Subgroup W) (H.map (MulAut.conj ψ).toMonoidHom) ≤
        commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) ⊓
          fixV (H.map (MulAut.conj φ).toMonoidHom) :=
      inf_le_inf_left _ hUψfix
    have hsum : E3.mQuot (commSub (commSub (⊤ : Subgroup W)
          (H.map (MulAut.conj φ).toMonoidHom)) (Subgroup.zpowers t) ⊔
          (commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) ⊓
            fixV (H.map (MulAut.conj φ).toMonoidHom)))
        (commSub (⊤ : Subgroup W) (H.map (MulAut.conj φ).toMonoidHom) ⊓
          fixV (H.map (MulAut.conj φ).toMonoidHom)) +
        E3.mQuot (commSub (commSub (⊤ : Subgroup W)
          (H.map (MulAut.conj ψ).toMonoidHom)) (Subgroup.zpowers t) ⊔
          (commSub (⊤ : Subgroup W) (H.map (MulAut.conj ψ).toMonoidHom) ⊓
            fixV (H.map (MulAut.conj ψ).toMonoidHom)))
        (commSub (⊤ : Subgroup W) (H.map (MulAut.conj ψ).toMonoidHom) ⊓
          fixV (H.map (MulAut.conj ψ).toMonoidHom)) ≤
        rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) :=
      mQuot_commSub_add_le_rk_commSub (W := W) t hstab0 hstabψ hint
    have hqψ : E3.mQuot (commSub (commSub (⊤ : Subgroup W)
          (H.map (MulAut.conj ψ).toMonoidHom)) (Subgroup.zpowers t) ⊔
          (commSub (⊤ : Subgroup W) (H.map (MulAut.conj ψ).toMonoidHom) ⊓
            fixV (H.map (MulAut.conj ψ).toMonoidHom)))
        (commSub (⊤ : Subgroup W) (H.map (MulAut.conj ψ).toMonoidHom) ⊓
          fixV (H.map (MulAut.conj ψ).toMonoidHom)) = 0 := by
      omega
    have hirrψ : commSub (⊤ : Subgroup W) (H.map (MulAut.conj ψ).toMonoidHom) ∈
        irrSet (H.map (MulAut.conj ψ).toMonoidHom) := by
      have h := ConjugateSection.map_mem_irrSet_map_conj (H := H) (φ := ψ) hirrH
      rwa [← s15_Infra_commSub_top_map_conj H ψ] at h
    exact mem_centralizer_of_m22_section_mQuot_eq_zero
      (W := W) (H := H.map (MulAut.conj ψ).toMonoidHom) (t := t)
      hW (isSpor_map_conj hM22H) hirrψ (hnorm ψ hψA) hqψ
  refine ⟨t, htAW, ht2, htne, hrkW, φ, hφA, hnorm φ hφA, houter0, ?_⟩
  intro ψ hψA
  exact hcent ψ hψA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
