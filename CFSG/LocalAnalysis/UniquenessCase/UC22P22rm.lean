module

import CFSG.Goldschmidt.Steps.Components
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

theorem uc22p22r_fstar_eq {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hN : IsSimpleGroup N) (hnab : ∃ a b : N, a * b ≠ b * a)
    (hC : centralizer (N : Set Y) = ⊥) : genFittingFStar Y = N := by
  obtain ⟨hO, h2, hL, -⟩ := CFSG.Goldschmidt.N8g Y N inferInstance hN hnab hC
  have hFit0 : CFSG.ComponentClassification.Fitting.subgroup Y = CFSG.Open.pCore 2 Y := by
    rw [CFSG.ComponentClassification.PrimeCore.fitting_eq_two_of_odd_corefree hO,
      CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup]
    rfl
  have hFit : CFSG.ComponentClassification.Fitting.subgroup Y = ⊥ := hFit0.trans h2
  show CFSG.ComponentClassification.GeneralizedFitting.subgroup Y = N
  rw [CFSG.ComponentClassification.GeneralizedFitting.subgroup.eq_sup, hFit, bot_sup_eq]
  exact hL

end CFSG.LocalAnalysis.UniquenessCase.UC22
