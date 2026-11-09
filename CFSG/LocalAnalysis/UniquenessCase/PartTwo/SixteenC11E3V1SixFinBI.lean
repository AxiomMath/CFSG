module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBT
import Mathlib.Tactic.FinCases

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv

private theorem sixInvTabs_complete_0_false : ∀ σ : Perm (Fin 6), σ 0 = 0 →
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, false⟩ ⟨σ, sixAlpha σ, false⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, false⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, false⟩ ∈ sixInvTabs := by
  decide +kernel

private theorem sixInvTabs_complete_0_true : ∀ σ : Perm (Fin 6), σ 0 = 0 →
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, true⟩ ⟨σ, sixAlpha σ, true⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, true⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, true⟩ ∈ sixInvTabs := by
  decide +kernel

private theorem sixInvTabs_complete_1_false : ∀ σ : Perm (Fin 6), σ 0 = 1 →
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, false⟩ ⟨σ, sixAlpha σ, false⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, false⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, false⟩ ∈ sixInvTabs := by
  decide +kernel

private theorem sixInvTabs_complete_1_true : ∀ σ : Perm (Fin 6), σ 0 = 1 →
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, true⟩ ⟨σ, sixAlpha σ, true⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, true⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, true⟩ ∈ sixInvTabs := by
  decide +kernel

private theorem sixInvTabs_complete_2_false : ∀ σ : Perm (Fin 6), σ 0 = 2 →
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, false⟩ ⟨σ, sixAlpha σ, false⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, false⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, false⟩ ∈ sixInvTabs := by
  decide +kernel

private theorem sixInvTabs_complete_2_true : ∀ σ : Perm (Fin 6), σ 0 = 2 →
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, true⟩ ⟨σ, sixAlpha σ, true⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, true⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, true⟩ ∈ sixInvTabs := by
  decide +kernel

private theorem sixInvTabs_complete_3_false : ∀ σ : Perm (Fin 6), σ 0 = 3 →
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, false⟩ ⟨σ, sixAlpha σ, false⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, false⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, false⟩ ∈ sixInvTabs := by
  decide +kernel

private theorem sixInvTabs_complete_3_true : ∀ σ : Perm (Fin 6), σ 0 = 3 →
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, true⟩ ⟨σ, sixAlpha σ, true⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, true⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, true⟩ ∈ sixInvTabs := by
  decide +kernel

private theorem sixInvTabs_complete_4_false : ∀ σ : Perm (Fin 6), σ 0 = 4 →
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, false⟩ ⟨σ, sixAlpha σ, false⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, false⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, false⟩ ∈ sixInvTabs := by
  decide +kernel

private theorem sixInvTabs_complete_4_true : ∀ σ : Perm (Fin 6), σ 0 = 4 →
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, true⟩ ⟨σ, sixAlpha σ, true⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, true⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, true⟩ ∈ sixInvTabs := by
  decide +kernel

private theorem sixInvTabs_complete_5_false : ∀ σ : Perm (Fin 6), σ 0 = 5 →
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, false⟩ ⟨σ, sixAlpha σ, false⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, false⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, false⟩ ∈ sixInvTabs := by
  decide +kernel

private theorem sixInvTabs_complete_5_true : ∀ σ : Perm (Fin 6), σ 0 = 5 →
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, true⟩ ⟨σ, sixAlpha σ, true⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, true⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, true⟩ ∈ sixInvTabs := by
  decide +kernel

theorem sixInvTabs_complete : ∀ (σ : Perm (Fin 6)) (ε : Bool),
    s1611e3_sixCodeMul ⟨σ, sixAlpha σ, ε⟩ ⟨σ, sixAlpha σ, ε⟩ = s1611e3_sixCodeOne →
    (⟨σ, sixAlpha σ, ε⟩ : s1611e3_SixCode) ≠ s1611e3_sixCodeOne →
    sixCodeTab ⟨σ, sixAlpha σ, ε⟩ ∈ sixInvTabs := by
  intro σ ε
  generalize ha : σ 0 = a
  fin_cases a <;> cases ε
  exacts [sixInvTabs_complete_0_false σ ha, sixInvTabs_complete_0_true σ ha, sixInvTabs_complete_1_false σ ha, sixInvTabs_complete_1_true σ ha, sixInvTabs_complete_2_false σ ha, sixInvTabs_complete_2_true σ ha, sixInvTabs_complete_3_false σ ha, sixInvTabs_complete_3_true σ ha, sixInvTabs_complete_4_false σ ha, sixInvTabs_complete_4_true σ ha, sixInvTabs_complete_5_false σ ha, sixInvTabs_complete_5_true σ ha]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
