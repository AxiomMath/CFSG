module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm34

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

section Intrinsic

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A X : Subgroup Γ}

theorem iThm34_of_cenIn_eq
    (h : NearAsolvAction p A X) {X₁ X₂ D : Subgroup Γ}
    (hP : (X₁, X₂) ∈ iPairs A X) (hD : cenIn X (A : Set Γ) = D)
    [((D ⊓ X₂).subgroupOf D).Normal] [((D ⊓ X₂).subgroupOf (D ⊓ X₁)).Normal] :
    fittingPre (D ⊓ X₁) (D ⊓ X₂) = fittingPre D (D ⊓ X₂) ∧
      IsChiefFactorOf D (fittingPre D (D ⊓ X₂)) (D ⊓ X₂) ∧
      ∀ M : Subgroup Γ, IsChiefFactorOf D M (D ⊓ X₂) → M = fittingPre D (D ⊓ X₂) := by
  subst hD
  exact iThm34 h hP

end Intrinsic

section Functor

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem fitting_minimal_normal'
    (hθ : NearFunctor p A θ) {X₁ X₂ : Subgroup G}
    (h : (X₁, X₂) ∈ pairsP p A θ)
    [((dsub A θ ⊓ X₂).subgroupOf (dsub A θ)).Normal]
    [((dsub A θ ⊓ X₂).subgroupOf (dsub A θ ⊓ X₁)).Normal] :
    fittingPre (dsub A θ ⊓ X₁) (dsub A θ ⊓ X₂) = fittingPre (dsub A θ) (dsub A θ ⊓ X₂) ∧
    IsChiefFactorOf (dsub A θ) (fittingPre (dsub A θ) (dsub A θ ⊓ X₂)) (dsub A θ ⊓ X₂) ∧
    ∀ M : Subgroup G, IsChiefFactorOf (dsub A θ) M (dsub A θ ⊓ X₂) →
      M = fittingPre (dsub A θ) (dsub A θ ⊓ X₂) := by
  have hXm : X₁ ⊔ dsub A θ ∈ mtil p A θ := sup_dsub_mem_mtil hθ h.1
  have hact : NearAsolvAction p A (X₁ ⊔ dsub A θ) :=
    { prime := hθ.prime
      odd := hθ.odd
      elemAbelian := hθ.elemAbelian
      admits := hXm.1.1
      nearPSolvable := hXm.1.2.2.2.1
      solvable_cen := hXm.1.2.2.2.2 }
  have hD : cenIn (X₁ ⊔ dsub A θ) (A : Set G) = dsub A θ := cenIn_eq_dsub_of_mem_mtil hθ hXm
  have hP : (X₁, X₂) ∈ iPairs A (X₁ ⊔ dsub A θ) := by
    have heq := pairsYX_eq_iPairsY (Y := X₂ ⊓ dsub A θ) hθ hXm
    have hP' : (X₁, X₂) ∈ iPairsY A (X₁ ⊔ dsub A θ) (X₂ ⊓ dsub A θ) := by
      rw [← heq]
      exact ⟨⟨h, rfl⟩, le_sup_left⟩
    exact hP'.1
  exact iThm34_of_cenIn_eq hact hP hD

end Functor

end CFSG.SignalizerFunctorTheorem.McBride.Near
