module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LocalAnalysis.UniquenessCase.UC6 (dataOfSetup4 isStronglyPEmbedded_of_clause_one)

variable {G : Type} [Group G] [Finite G]

theorem three_mem_uniqueFourSigma_of_mem_uniqueFourBeta (S : Setup4 G) (hσ : S.InMSigma)
    (h3 : 3 ∈ uniqueFourBeta G) : 3 ∈ uniqueFourSigma S.M :=
  (hσ.1 h3) ▸ S.hp

theorem isStronglyPEmbedded_three_of_mem_uniqueFourBeta (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (h3 : 3 ∈ uniqueFourBeta G) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M := by
  have h3M : 3 ∈ uniqueFourSigma S.M := three_mem_uniqueFourSigma_of_mem_uniqueFourBeta S hσ h3
  obtain ⟨-, hM0, -, P, -, -, hcl⟩ := (hU S.M S.maxLocal ⟨3, h3M⟩).1 3 h3M
  rcases hcl with ⟨hdvd, hstrong⟩ | ⟨h5, -⟩
  · exact isStronglyPEmbedded_of_clause_one hM0 hdvd hstrong
  · omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
