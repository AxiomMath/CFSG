module

public import CFSG.LocalAnalysis.UniqueFourCatalog.ClosureTop
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureUnitModel
import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC (tvSetSU tvSetSU_conj exists_tvSetSU_not_scalar
  tvSetSU_subset_twoLocalClosure)

theorem closureTop_of_PSU {G : Type} [Group G] [IsSimpleGroup G] {n f : ℕ} (hn : 3 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2)
    (e : G ≃* StatedProj (StatedSU n (2 ^ f) K)) : ClosureTop G := by
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := f) hK
  exact closureTop_of_proj_gen (StatedSU n (2 ^ f) K) e (tvSetSU hK n)
    (tvSetSU_conj hK) (exists_tvSetSU_not_scalar hK hn)
    (fun E P hE hP hP2 hEN => tvSetSU_subset_twoLocalClosure hK hn E P hE hP hP2 hEN)

theorem not_uniqueFour_of_statedPSU {G : Type} [Group G] [Finite G]
    (hS : CFSG.Yardstones.Mf4cdcdf2e013.Standing4 G) {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU n 2 f) :
    ¬ CFSG.Open.uniqueFourUnique G := by
  obtain ⟨⟨-, -, hn, -⟩, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have := hS.simple
  exact not_uniqueFour_of_closureTop hS (closureTop_of_PSU hn hcard e)

end CFSG.LocalAnalysis.UniqueFourCatalog
