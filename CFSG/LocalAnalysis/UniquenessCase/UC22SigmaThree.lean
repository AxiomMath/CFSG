module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LocalAnalysis.UniquenessCase.UC6 (dataOfSetup4 isStronglyPEmbedded_of_clause_one)

variable {G : Type} [Group G] [Finite G]

theorem three_not_mem_uniqueFourBeta (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hk : (dataOfSetup4 hS hU S).k = 2) :
    3 ∉ uniqueFourBeta G := by
  intro h3
  have hp : S.p = 3 := hσ.1 h3
  have h3M : 3 ∈ uniqueFourSigma S.M := hp ▸ S.hp
  obtain ⟨-, hM0, -, P, -, -, hcl⟩ := (hU S.M S.maxLocal ⟨3, h3M⟩).1 3 h3M
  rcases hcl with ⟨hdvd, hstrong⟩ | ⟨h5, -⟩
  · have hSE : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M :=
      isStronglyPEmbedded_of_clause_one hM0 hdvd hstrong
    have h1 : (dataOfSetup4 hS hU S).k = 1 := by
      show CFSG.LocalAnalysis.RankThreeUC.kParam S.M = 1
      rw [CFSG.LocalAnalysis.RankThreeUC.kParam, if_pos hSE]
    omega
  · omega

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
