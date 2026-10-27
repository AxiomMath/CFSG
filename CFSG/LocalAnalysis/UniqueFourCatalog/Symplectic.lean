module

public import CFSG.LocalAnalysis.UniqueFourCatalog.ClosureTop
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureSymplectic
import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureExcBasic

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC (twoLocalClosure twoLocalClosure_eq_top_of_equiv)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

theorem closureTop_of_PSp {G : Type} [Group G] [IsSimpleGroup G] {n : ℕ} (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : G ≃* StatedProj (StatedSp n K)) : ClosureTop G := by
  intro E S₀ hE hS₀ hS₀2 hEN
  let Φ : G ≃* CFSG.LocalAnalysis.RankThreeUC.SpClosure.isom
      (CFSG.LocalAnalysis.RankThreeUC.SpClosure.spB n K) :=
    e.trans (CFSG.LocalAnalysis.RankThreeUC.SpClosure.spModelEquiv hn)
  have : IsSimpleGroup (CFSG.LocalAnalysis.RankThreeUC.SpClosure.isom
      (CFSG.LocalAnalysis.RankThreeUC.SpClosure.spB n K)) := Φ.symm.isSimpleGroup
  refine twoLocalClosure_eq_top_of_equiv Φ E ?_
  refine CFSG.LocalAnalysis.RankThreeUC.SpClosure.twoLocalClosure_eq_top_isom
    CFSG.LocalAnalysis.RankThreeUC.SpClosure.spB_isAlt
    CFSG.LocalAnalysis.RankThreeUC.SpClosure.spB_nondegenerate
    (CFSG.LocalAnalysis.RankThreeUC.SpClosure.spB₀ n K)
    CFSG.LocalAnalysis.RankThreeUC.SpClosure.spB₀_add_swap
    (E.map Φ.toMonoidHom) (S₀.map Φ.toMonoidHom) ?_ ?_ (hS₀2.map Φ.toMonoidHom) ?_
  · rwa [Subgroup.card_map_of_injective Φ.injective]
  · intro hbot
    exact hS₀ ((Subgroup.map_eq_bot_iff_of_injective S₀ Φ.injective).1 hbot)
  · exact (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map Φ.toMonoidHom)

theorem not_uniqueFour_of_statedPSp {G : Type} [Group G] [Finite G] (hS : Standing4 G) {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSp n 2 f) : ¬ uniqueFourUnique G := by
  obtain ⟨⟨-, -, hn, -⟩, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have hC : CharP K 2 := CFSG.LocalAnalysis.RankThreeUC.charP_two_of_card hcard
  have hSimple : IsSimpleGroup G := hS.simple
  exact not_uniqueFour_of_closureTop hS (closureTop_of_PSp (by omega) e)

end CFSG.LocalAnalysis.UniqueFourCatalog
