module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary

public section

namespace CFSG

namespace BenderSuzuki

open Matrix
open BenderSuzuki.MatrixGroups

private theorem szModel_eq_suzukiMatrixGroup_of_eq
    (n : ℕ)
    (T : Subgroup (GL (Fin 4) (GaloisField 2 (2 * n + 1))))
    (hT : T = SzModel n) :
    T = SuzukiMatrixGroup n := by
  rw [hT]
  apply congrArg Subgroup.closure
  ext A
  simp only [SzGenerators, SuzukiMatrixGeneratorSet, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨a, b, hab⟩ | ⟨x, hx⟩ | hw)
    · left
      refine ⟨a, b, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      have hij := congrArg (fun M => M i j) hab
      simpa [SuzukiRootGL, SuzukiRootMatrix] using hij
    · right
      left
      refine ⟨x, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      have hij := congrArg (fun M => M i j) hx
      simpa [SuzukiTorusGL, SuzukiTorusMatrix] using hij
    · right
      right
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      have hij := congrArg (fun M => M i j) hw
      simpa [SuzukiWeylGL, SuzukiWeylMatrix] using hij
  · rintro (⟨a, b, rfl⟩ | ⟨x, rfl⟩ | rfl)
    · left
      exact ⟨a, b, by simp [SuzukiRootGL, SuzukiRootMatrix]⟩
    · right
      left
      exact ⟨x, by simp [SuzukiTorusGL, SuzukiTorusMatrix]⟩
    · right
      right
      simp [SuzukiWeylGL, SuzukiWeylMatrix]

theorem szModel_eq_suzukiMatrixGroup (n : ℕ) : SzModel n = SuzukiMatrixGroup n :=
  szModel_eq_suzukiMatrixGroup_of_eq n _ rfl

end BenderSuzuki

end CFSG
