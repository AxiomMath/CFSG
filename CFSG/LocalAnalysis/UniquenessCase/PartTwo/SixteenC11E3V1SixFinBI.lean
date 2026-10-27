module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv

theorem sixInvTabs_complete : ∀ (σ : Perm (Fin 6)) (ε : Bool),
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, ε⟩ ⟨σ, sixAlpha σ, ε⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, ε⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, ε⟩ ∈ sixInvTabs := by
  decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
