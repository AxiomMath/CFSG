module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22tcU
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20s

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22um_le_M_of_lt (D : Data G) (h20_4 : S20_4 D) (h1930 : H1930 D) {L Y : Subgroup G}
    (hL : L ∈ calLLow D.T D.M) (hTY : D.T ≤ Y) (hYL : Y < L ⊔ D.T) : Y ≤ D.M := by
  by_contra hYM
  have hLcal : L ∈ calL D.T D.M := hL.prop
  have hY : Y ∈ hSet D.T D.M := ⟨hTY, hYM, uc22p20s_centralizer_le hLcal hTY hYL.le⟩
  obtain ⟨L', hL'⟩ := uc22p20s_calLOf_nonempty D h20_4 h1930 hY
  have hL'cal : L' ∈ calL D.T D.M := hL'.1
  have hL'Y : L' ≤ Y := hL'.2.le
  have hL'L : L' ≤ L :=
    uc22p20m_le_of_perfect_sup hL'cal.2.1 (hL'Y.trans hYL.le) hLcal.1 D.sylowM.isPGroup
  have hLL' : L ≤ L' := hL.2 hL'cal hL'L
  exact hYL.not_ge (sup_le (hLL'.trans hL'Y) hTY)

theorem uniqueMaxL0T_of_s20_4 (D : Data G) (Ch : Choice2011 G) (h20_4 : S20_4 D) :
    UniqueMaxL0T D Ch := by
  intro h1930 c
  have hLcal : c.L0 ∈ calL D.T D.M := c.hL0.prop
  refine ⟨D.M ⊓ (c.L0 ⊔ D.T), le_inf D.sylowM.le le_sup_right,
    lt_of_le_of_ne inf_le_right fun h => hLcal.2.2.1.2.1 (h ▸ inf_le_left), fun Y hTY hYL => ?_⟩
  exact le_inf (uc22um_le_M_of_lt D h20_4 h1930 c.hL0 hTY hYL) hYL.le

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
