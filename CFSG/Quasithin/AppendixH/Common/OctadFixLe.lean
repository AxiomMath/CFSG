module

public import CFSG.Quasithin.AppendixH.Common.OctadPtStabCard

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

theorem eq_of_octFix_le_octStab {O O' : Finset (Fin 24)}
    (hO : IsOctad O) (hO' : IsOctad O') (h : octFix O' ≤ octStab O) : O' = O := by
  by_contra hne
  have hp : ∃ p, p ∈ O ∧ p ∉ O' := by
    by_contra hcon
    have hsub : O ⊆ O' := by
      intro p hpO
      by_contra hpO'
      exact hcon ⟨p, hpO, hpO'⟩
    exact hne (Finset.eq_of_subset_of_card_le hsub (by simp [hO.1, hO'.1])).symm
  obtain ⟨p, hpO, hpO'⟩ := hp
  have hmem : ∀ i, i ∉ O' → i ∈ O := by
    intro i hi
    obtain ⟨g, hg, -⟩ := octFix_regular hO' (i := p) (j := i) hpO' hi
    have hgstab : (g : S24) ∈ octStab O := h g.2
    obtain ⟨-, hgO⟩ := mem_octStab_iff.1 hgstab
    have hgpO : (g : S24) p ∈ O := by
      rw [← hgO, smul_finset_eq_map, Finset.mem_map_equiv]
      simpa using hpO
    rw [hg] at hgpO
    exact hgpO
  have hcompl : (O'ᶜ : Finset (Fin 24)) ⊆ O := fun i hi => hmem i (Finset.mem_compl.1 hi)
  have hcard := Finset.card_le_card hcompl
  rw [Finset.card_compl, hO'.1, Fintype.card_fin, hO.1] at hcard
  norm_num at hcard

end CFSG.ASVolI.AppH
