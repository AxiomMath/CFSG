module

public import CFSG.RankThree.PartOne.KF.ClassifyTags
public import CFSG.RankThree.PartOne.KF.ClsPSUSmall
public import CFSG.RankThree.PartOne.KF.ClsPSUSix
public import CFSG.RankThree.PartOne.KF.ClsPSUBig
public import CFSG.RankThree.PartOne.KF.ClsSULift

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)

theorem kf123ClassifyTag_PSU
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF123ClassifyTag .PSU := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hcl : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hn3 : 3 ≤ n := hadm.2.2.1
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with rfl | rfl | rfl | rfl | hn7
  · exact (psu_three_false h hcl).elim
  · exact psu_four_row h hcl
  · refine psu_five_row h hcl fun {K} _ _ _ hU h25 => ?_
    have := KFU.le_localRank_statedSU_lift hU Nat.prime_five (by norm_num) (by simpa using h25)
      (dvd_refl 5) (by norm_num) (by norm_num)
    simpa using this
  · exact (psu_six_false hGA h hcl).elim
  · exact (psu_large_false hGA h hn7 hcl).elim

end CFSG.RankThree.PartOne
