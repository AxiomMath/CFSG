module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm34Quot

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A X Y : Subgroup Γ}

theorem iThm34
    (h : NearAsolvAction p A X) {X₁ X₂ : Subgroup Γ} (hP : (X₁, X₂) ∈ iPairs A X)
    [((cenIn X (A : Set Γ) ⊓ X₂).subgroupOf (cenIn X (A : Set Γ))).Normal]
    [((cenIn X (A : Set Γ) ⊓ X₂).subgroupOf (cenIn X (A : Set Γ) ⊓ X₁)).Normal] :
    fittingPre (cenIn X (A : Set Γ) ⊓ X₁) (cenIn X (A : Set Γ) ⊓ X₂) =
        fittingPre (cenIn X (A : Set Γ)) (cenIn X (A : Set Γ) ⊓ X₂) ∧
      IsChiefFactorOf (cenIn X (A : Set Γ)) (fittingPre (cenIn X (A : Set Γ))
        (cenIn X (A : Set Γ) ⊓ X₂)) (cenIn X (A : Set Γ) ⊓ X₂) ∧
      ∀ M : Subgroup Γ, IsChiefFactorOf (cenIn X (A : Set Γ)) M (cenIn X (A : Set Γ) ⊓ X₂) →
        M = fittingPre (cenIn X (A : Set Γ)) (cenIn X (A : Set Γ) ⊓ X₂) := by
  obtain ⟨hCS, hcen⟩ := Thm34.chiefSetting_qimg h hP
  obtain ⟨ha, hb, hc⟩ := Thm34.core34 hCS hcen
  have hch := Thm32.chief_of_mem_iPairsY
    (⟨hP, rfl⟩ : (X₁, X₂) ∈ iPairsY A X (X₂ ⊓ cenIn X (A : Set Γ)))
  exact Thm34.thm34_of_quotient ((le_sup_right.trans le_sup_left).trans hch.1.2)
    (le_sup_left.trans (le_sup_left.trans hch.1.2)) hch.2.2.1.le ha hb hc

end CFSG.SignalizerFunctorTheorem.McBride.Near
