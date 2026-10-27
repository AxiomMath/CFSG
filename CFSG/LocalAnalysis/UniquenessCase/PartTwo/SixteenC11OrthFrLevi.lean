module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrLeviC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrLeviB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open scoped Matrix

theorem s16c11_fr_levi_surjective_kernel {m : ℕ} (hm : m = 3 ∨ m = 4) :
    Function.Surjective (s16c11_fr_leviHom hm) ∧
      IsPGroup 2 ↥(s16c11_fr_leviHom hm).ker :=
  ⟨s16c11_fr_levi_surjective hm, s16c11_fr_levi_kernel hm⟩

theorem s16c11_fr_levi {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ∃ π : ↥(s16c11FrK m) →* ↥(S16C11FrO (m - 2)),
      Function.Surjective π ∧ IsPGroup 2 ↥π.ker := by
  exact ⟨s16c11_fr_leviHom hm, s16c11_fr_levi_surjective_kernel hm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
