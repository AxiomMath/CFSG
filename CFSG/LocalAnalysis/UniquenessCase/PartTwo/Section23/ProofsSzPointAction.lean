module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SzInnerTorusFactsOfPoint
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSzPointActionTorus
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.BenderSuzuki.MatrixGroups

private theorem exists_mulEquiv_suzukiMatrixGroup {X : Type} [Group X] [Finite X] {f : ℕ}
    (hSz : IsSz X f) :
    ∃ m : ℕ, 0 < m ∧ f = 2 * m + 1 ∧ Nonempty (X ≃* SuzukiMatrixGroup m) := by
  obtain ⟨m, hm, hf, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 hSz
  exact ⟨m, by omega, hf,
    ⟨e.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv m)⟩⟩

theorem szPointActionFacts_holds : SzPointActionFacts := by
  intro X _ _ f hSz
  obtain ⟨m, hm, hf, ⟨e⟩⟩ := exists_mulEquiv_suzukiMatrixGroup hSz
  rw [hf]
  exact CFSG.GroupTheory.SuzukiTorusData.of_mulEquiv e
    (suzukiTorusData_suzukiMatrixGroup m hm)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
