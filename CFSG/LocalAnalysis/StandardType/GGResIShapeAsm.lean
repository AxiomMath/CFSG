module

public import CFSG.LocalAnalysis.StandardType.GGResICellSound
public import CFSG.LocalAnalysis.StandardType.GGResIICell
public import CFSG.LocalAnalysis.StandardType.GGResICellNat

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResI_shape_ok {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ}
    {L : List ℕ} (hL : ∀ q ∈ L, q.Prime) {Tr : GGTreeI n}
    (hchk : checkTreeI ((L.map (· ^ 20)).prod) (ggStdTableSymI C ib ic e₁ e₂) ib [] Tr = true)
    (h3 : ∃ wits : List (ℕ × ℕ × GGCellWitI n), GGCellCheckI 3 C ib ic e₁ e₂ wits)
    (hcells : ∀ q ∈ L, q ≠ 2 → q ≠ 3 → ∀ [NeZero q],
      ∃ wits : List (ℕ × ℕ × GGCellWitI n), GGCellCheckI q C ib ic e₁ e₂ wits) :
    GGResIShapeOK C ib ic e₁ e₂ := by
  intro p _ V _ _ _ _ g h α x u v hp2 hg h2 hT hspan hind _ hfix _
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨wits, hcell⟩ := h3
    exact ggResI_cell_sound hcell hp2 hg h2 hT hspan hind hfix
  · by_cases hpL : p ∈ L
    · obtain ⟨wits, hcell⟩ := hcells p hpL hp2 hp3
      exact ggResI_cell_sound hcell hp2 hg h2 hT hspan hind hfix
    · have hpp : p.Prime := Fact.out
      have hp5 : 5 ≤ p := by
        by_contra hlt
        push Not at hlt
        interval_cases p
        all_goals first
          | exact absurd rfl hp2
          | exact absurd rfl hp3
          | exact absurd hpp (by norm_num)
      exact Or.inl (ggResI_checkTree_sound hp5 (ggResII_prod_ne_zero hL 20 hpL) hg h2 hT hspan hind
        Tr [] hchk (by simp))

end CFSG.StandardType
