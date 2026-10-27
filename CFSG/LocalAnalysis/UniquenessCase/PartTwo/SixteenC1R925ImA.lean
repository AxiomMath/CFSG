module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Kbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Alt5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem r925_card_eq_sixty_of_isAlt_five {X : Type} [Group X] (h : IsAlt X 5) :
    Nat.card X = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem r925_sixty_dvd_card_of_isPerfA5Cover {X : Type} [Group X] [Finite X]
    (h : IsPerfA5Cover X) : 60 ∣ Nat.card X := by
  obtain ⟨-, Z, hZn, -, he⟩ := h
  haveI := hZn
  have hcard : Nat.card X = Nat.card (X ⧸ Z) * Nat.card Z :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  rw [hcard, r925_card_eq_sixty_of_isAlt_five he]
  exact dvd_mul_right 60 (Nat.card Z)

private theorem r925_im_alt5_hmap {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) (hle : K.map (toModO3p Γ) ≤ M.map (toModO3p Γ)) :
    CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840) ↥(K.map (toModO3p Γ)) :=
  r925_kGroupNonab_map (toModO3p Γ) (isoInvariant_dvdOrThreeFree 51840) h.m_catalogue hle

private theorem r925_im_alt5_hDvd {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) (hle : K.map (toModO3p Γ) ≤ M.map (toModO3p Γ)) :
    Nat.card ↥(K.map (toModO3p Γ)) ∣ 51840 ∨ ¬ 3 ∣ Nat.card ↥(K.map (toModO3p Γ)) := by
  haveI : IsSimpleGroup ↥(K.map (toModO3p Γ)) := r925_kbar_simple h
  exact CFSG.KCore.KGroupNonab.catalogue_self (isoInvariant_dvdOrThreeFree 51840)
    (r925_im_alt5_hmap h hle) (r925_kbar_nonabelian h)

private theorem r925_im_alt5_three_dvd {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) : 3 ∣ Nat.card ↥(K.map (toModO3p Γ)) := by
  obtain ⟨D, hDY, hD3⟩ := h.y_cover.exists_subgroup_card_three
  have hDbar : Nat.card (D.map (toModO3p Γ)) = 3 :=
    r925_card_map_eq_three r925_pPrimeCore_orderOf hD3
  have h3dvdD : 3 ∣ Nat.card ↥(D.map (toModO3p Γ)) := ⟨1, by rw [hDbar, mul_one]⟩
  exact dvd_trans h3dvdD (Subgroup.card_dvd_of_le
    (Subgroup.map_mono (f := toModO3p Γ) (hDY.trans h.y_le_k)))

private theorem r925_im_alt5_card_dvd {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) (hle : K.map (toModO3p Γ) ≤ M.map (toModO3p Γ)) :
    Nat.card ↥(K.map (toModO3p Γ)) ∣ 51840 := by
  rcases r925_im_alt5_hDvd h hle with hd | hd
  · exact hd
  · exact absurd (r925_im_alt5_three_dvd h) hd

private theorem r925_im_alt5_isAlt
    (hK32 : UCK.K32) {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) (hle : K.map (toModO3p Γ) ≤ M.map (toModO3p Γ)) :
    IsAlt ↥(K.map (toModO3p Γ)) 5 := by
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(K.map (toModO3p Γ))) = 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (K.map (toModO3p Γ))]
    exact r925_kbar_pRank h
  exact r925_alt5_of_dvd hK32 (r925_kbar_kgroup h) (r925_kbar_simple h)
    (r925_kbar_nonabelian h) hrank (r925_im_alt5_card_dvd h hle)

private theorem r925_im_alt5_eq {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) (hAlt : IsAlt ↥(K.map (toModO3p Γ)) 5) :
    Y.map (toModO3p Γ) = K.map (toModO3p Γ) := by
  have hYcover : IsPerfA5Cover ↥(Y.map (toModO3p Γ)) :=
    r925_perfA5Cover_map_mk (J := CFSG.pPrimeCore 3 Γ) r925_pPrimeCore_orderOf h.y_cover
  have h60 : 60 ∣ Nat.card ↥(Y.map (toModO3p Γ)) :=
    r925_sixty_dvd_card_of_isPerfA5Cover hYcover
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono h.y_le_k) ?_
  rw [r925_card_eq_sixty_of_isAlt_five hAlt]
  exact Nat.le_of_dvd Nat.card_pos h60

theorem r925_im_alt5
    (hK32 : UCK.K32) {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) (hle : K.map (toModO3p Γ) ≤ M.map (toModO3p Γ)) :
    IsAlt ↥(K.map (toModO3p Γ)) 5 ∧ Y.map (toModO3p Γ) = K.map (toModO3p Γ) := by
  have hAlt := r925_im_alt5_isAlt hK32 h hle
  exact ⟨hAlt, r925_im_alt5_eq h hAlt⟩

theorem r925_im_not_le {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) (hle : K.map (toModO3p Γ) ≤ M.map (toModO3p Γ)) :
    ¬ CFSG.pPrimeCore 3 Γ ≤ M := by
  intro hJ
  have hKle : K ≤ (M.map (toModO3p Γ)).comap (toModO3p Γ) :=
    Subgroup.map_le_iff_le_comap.mp hle
  have hcomap : (M.map (toModO3p Γ)).comap (toModO3p Γ) = M ⊔ CFSG.pPrimeCore 3 Γ := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  rw [hcomap] at hKle
  have htop : (⊤ : Subgroup Γ) ≤ M ⊔ CFSG.pPrimeCore 3 Γ := by
    rw [← r925_sup_eq_top h]
    exact sup_le hKle le_sup_left
  have hMtop : M = ⊤ := by
    rw [sup_eq_left.mpr hJ] at htop
    exact top_le_iff.mp htop
  exact h.m_ne_top hMtop

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
