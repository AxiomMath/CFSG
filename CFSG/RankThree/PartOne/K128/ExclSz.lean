module

public import CFSG.RankThree.PartOne.KF.F128Syl
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.RankThree.PartOne.K128.TorusShape

public section

namespace CFSG.RankThree.PartOne.K128

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly (evenRank)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem kf128SylTag_twistedG2 : KF128SylTag .twistedG2 := by
  intro J _ _ _ _ T _ _ π _ _ p _ _ _ _ n f₀ _ hM
  exfalso
  have hadm := statedLieAdmissible_of_lieModel hM
  exact absurd hadm.2.2.2.1 (by norm_num)

theorem kf128SylTag_Tits : KF128SylTag .Tits := by
  intro J _ _ _ _ T _ _ π _ _ p hp hp5 _ _ n f₀ _ hM
  exfalso
  have hadm := statedLieAdmissible_of_lieModel hM
  have h1 : p * f₀ = 1 := hadm.2.2.2.2
  have : p ∣ 1 := ⟨f₀, h1.symm⟩
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

theorem kf128SylTag_twistedB2 : KF128SylTag .twistedB2 := by
  intro J _ _ _ _ T _ _ π _ _ p hp hp5 _ _ n f₀ _ hM α _ _ _ _ _ hrk
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hS : SuzukiModel T 2 (p * f₀) := by
    rcases hM with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hS
  obtain ⟨-, a, ha, K, _, _, hfa, hcard, ⟨e⟩⟩ := hS
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hcard, hfa]
  let e' : T ≃* CFSG.Open.GLASzGroup a K :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K))
  have hsyl := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    a ha hK' e' p (by omega)
  have := pRank_le_one_of_cyclic_sylow hsyl
  omega

end CFSG.RankThree.PartOne.K128
