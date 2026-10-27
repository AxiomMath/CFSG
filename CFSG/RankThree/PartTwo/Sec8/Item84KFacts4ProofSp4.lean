module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairModels
import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofSp4Conj

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item84KFacts4

open CFSG.Assembly.LowTwoRank

theorem kF84Sp4ThreeCent_holds : Item8KFacts3.KF84Sp4ThreeCent := by
  intro F _ _ _ hF4 y hy
  set e := CFSG.LieType.SteinbergBR.EvenSp.projEquiv (K := F) (n := 2) (by norm_num) with he
  have hy3 : e y ^ 3 = 1 := by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  have hy1 : e y ≠ 1 := by
    intro h
    have h1 : y = 1 := e.injective (h.trans (map_one e).symm)
    rw [h1, orderOf_one] at hy
    exact absurd hy (by norm_num)
  obtain ⟨ι⟩ := nonempty_perfectResidual_centralizer_sp4 hF4 hy3 hy1
  exact ⟨(Sec21.Item228Census3Proof.perfectResidualCentralizerEquiv e y).trans ι⟩

end CFSG.RankThree.PartTwo.Sec8.Item84KFacts4
