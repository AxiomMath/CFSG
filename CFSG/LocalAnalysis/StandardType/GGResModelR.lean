module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nMR_rowSeven_le_nonLevi {G : Type} [Group G] {p : ℕ} {J X : Subgroup G}
    (h : GGResRowAt ggRowSeven p J X) : GGResRowAt ggRowNonLevi p J X := by
  obtain ⟨a, c, ha, hc, hJ, hX, hr⟩ := h
  exact ⟨a, c, ha, hc, hJ, hX, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))⟩

theorem ggResModelInputR_of_tbjR (hJ : GGTBJInputR)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K)) :
    GGResModelInputR := by
  intro G _ _ p B Bs x L D J y K hH hp
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hJL := (hJ G p B Bs x L D J y K hH).1
  have hJK := (hJ G p B Bs x L D J y K hH).2
  rcases (hX G p B Bs x L D J y K hH).1 with hXL | hSL
  · rcases (hX G p B Bs x L D J y K hH).2 with hXK | hSK
    · rcases hJL hXL with hL | hL3 | hNL
      · rcases hJK hXK with hK | hK3 | hNK
        · exact Or.inl (ggResLeviDatum_of_sides_conj hp2 hL hK)
        · exact Or.inr (Or.inr (Or.inl
            (ggResLeviDatumLE3_of_sides_conj hp2 hK3 (Or.inl hL))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hNK)))
      · rcases hJK hXK with hK | hK3 | hNK
        · exact Or.inr (Or.inl (ggResLeviDatumLE3_of_sides_conj hp2 hL3 (Or.inl hK)))
        · exact Or.inr (Or.inl (ggResLeviDatumLE3_of_sides_conj hp2 hL3 (Or.inr hK3)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hNK)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hNL)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (l05nMR_rowSeven_le_nonLevi hSK))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (l05nMR_rowSeven_le_nonLevi hSL))))

end CFSG.StandardType

end
