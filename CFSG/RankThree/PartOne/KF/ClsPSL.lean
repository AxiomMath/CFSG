module

public import CFSG.RankThree.PartOne.KF.ClassifyTags
public import CFSG.RankThree.PartOne.KF.ClsPSLSmall
public import CFSG.RankThree.PartOne.KF.ClsPSLBig

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)

theorem kf123ClassifyTag_PSL
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF123ClassifyTag .PSL := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hcl : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL n 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  rcases Nat.lt_or_ge n 5 with hn | hn
  · rcases psl_small_cases h (by omega) hcl with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
    · exact ⟨1, le_rfl, by norm_num, by norm_num, f, hadm.2.1, hp, hcl⟩
    · exact ⟨8, by norm_num, by norm_num, by norm_num, f, hadm.2.1, hp, hcl⟩
  · exact (psl_large_false hGA h hn hcl).elim

end CFSG.RankThree.PartOne
