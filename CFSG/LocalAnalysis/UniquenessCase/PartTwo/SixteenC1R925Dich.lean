module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Kbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem r925_dich (hOdd : OddIdxAll) {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) (hnot : ¬ K.map (toModO3p Γ) ≤ M.map (toModO3p Γ)) :
    IsL3Five ↥(K.map (toModO3p Γ)) ∧ IsSL2Prime ↥(Y.map (toModO3p Γ)) 5 := by
  haveI : K.Normal := h.normal_k
  have hJ : ∀ x ∈ CFSG.pPrimeCore 3 Γ, ¬ 3 ∣ orderOf x := r925_pPrimeCore_orderOf
  obtain ⟨D, hDY, hD3⟩ := h.y_cover.exists_subgroup_card_three
  have hDM : D ≤ M := hDY.trans h.y_le
  exact hOdd (ModO3p Γ) (K.map (toModO3p Γ)) (K.map (toModO3p Γ) ⊓ M.map (toModO3p Γ))
    (Y.map (toModO3p Γ)) (D.map (toModO3p Γ)) (r925_kbar_kgroup h) (r925_kbar_simple h)
    (r925_kbar_nonabelian h) (r925_kbar_pRank h) inf_le_left
    (fun heq => hnot (inf_eq_left.mp heq))
    (r925_odd_relIndex_map (toModO3p Γ) (QuotientGroup.mk'_surjective _) h.normal_k h.m_odd)
    (r925_card_map_eq_three hJ hD3) (Subgroup.map_mono hDY)
    (le_inf (Subgroup.map_mono h.y_le_k) (Subgroup.map_mono h.y_le))
    (inf_le_inf_left _ (r925_normalizer_map_le hJ hD3 (h.m_normalizer D hDM hD3)))
    (r925_perfA5Cover_map_mk hJ h.y_cover)
    (r925_kGroupNonab_map (toModO3p Γ) (isoInvariant_dvdOrThreeFree 51840) h.m_catalogue
      inf_le_right)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
