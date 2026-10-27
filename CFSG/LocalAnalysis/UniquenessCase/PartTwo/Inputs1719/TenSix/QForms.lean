module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.QDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.Reduce

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

theorem w4Lem10_6Q_of_residualQ
    (h : W4Lem10_6ResidualQ) : W4Lem10_6Q := by
  intro W _ _ hW Y L p e q hLY hLn hF hLq hO2 _ _ _ _ hq3 hIn
  rcases hIn with ⟨t, n, p', e', hp', hp2', he', rfl, hmodel⟩ | ⟨rfl, -⟩
  · by_cases hpsl : t = .PSL ∧ n = 2
    · obtain ⟨rfl, rfl⟩ := hpsl
      exact w4Lem10_6_psl2 hW hLY hLn hF hLq hO2 hp2' hmodel
    · exact h W hW Y L t n p' e' hLY hLn hF hLq hO2 hp' hp2' he' hpsl hmodel hq3
  · exact absurd hq3 (lt_irrefl 3)

theorem w4Lem10_5Q_of_residualQ
    (h74 : W4Lem7_4) (h : W4Lem10_5ResidualQ) : W4Lem10_5Q := by
  intro W _ _ hW Y L p e q hLY hLn hF hLq hO2 hp hp2 he hq hq3 hIn
  rcases hIn with ⟨t, n, p', e', hp', hp2', he', hq', hmodel⟩ | ⟨rfl, -⟩
  · obtain ⟨rfl, rfl⟩ : p = p' ∧ e = e' :=
      Nat.Prime.pow_inj' hp hp' (by omega) (by omega) (by rw [← hq, hq'])
    by_cases hpsl : t = .PSL ∧ n = 2
    · obtain ⟨rfl, rfl⟩ := hpsl
      exact w4Lem10_5_psl2 h74 hW hLY hLn hF hLq hO2 hp hp2 he hmodel
    · exact h W hW Y L t n p e hLY hLn hF hLq hO2 hp hp2 he hpsl hmodel (hq ▸ hq3)
  · exact absurd hq3 (lt_irrefl 3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
