module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSp
public import CFSG.Open.StatedDefs

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

lemma sASp_lift_to_mem {X : Type} [Group X] (n : ℕ) (F : Type) [Field F]
    (ψ : ↥(CFSG.Open.StatedSp n F) →* X) {b : X} {s : GL (Fin n ⊕ Fin n) F}
    (hsP : s ∈ CFSG.Open.StatedSp n F)
    (hs : IsGLLift (CFSG.Open.StatedSp n F).subtype ψ s b) :
    ∃ s₀ : ↥(CFSG.Open.StatedSp n F),
      (s₀ : GL (Fin n ⊕ Fin n) F) = s ∧ ∀ u, b⁻¹ * ψ u * b = ψ (s₀ * u * s₀⁻¹) := by
  refine ⟨⟨s, hsP⟩, rfl, fun u => ?_⟩
  obtain ⟨u', hu'j, hu'ψ⟩ := hs u
  have heq : u' = (⟨s, hsP⟩ : ↥(CFSG.Open.StatedSp n F)) * u *
      (⟨s, hsP⟩ : ↥(CFSG.Open.StatedSp n F))⁻¹ := by
    apply Subgroup.subtype_injective
    rw [hu'j]
    rfl
  rw [hu'ψ, heq]

lemma sASp_lift_unique {X : Type} [Group X] (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (ψ : ↥(CFSG.Open.StatedSp n F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp n F)) {b : X}
    {s s' : GL (Fin n ⊕ Fin n) F} (hsP : s ∈ CFSG.Open.StatedSp n F)
    (hs'P : s' ∈ CFSG.Open.StatedSp n F)
    (hs : IsGLLift (CFSG.Open.StatedSp n F).subtype ψ s b)
    (hs' : IsGLLift (CFSG.Open.StatedSp n F).subtype ψ s' b) : s = s' := by
  obtain ⟨s₀, hs₀, hsl₀⟩ := sASp_lift_to_mem n F ψ hsP hs
  obtain ⟨s₁, hs₁, hsl₁⟩ := sASp_lift_to_mem n F ψ hs'P hs'
  have hconj : ∀ u, ψ (s₀ * u * s₀⁻¹) = ψ (s₁ * u * s₁⁻¹) := by
    intro u
    rw [← hsl₀ u, ← hsl₁ u]
  have hEq : s₀ = s₁ := conj_eq_unique_PSp n F ψ hψ hconj
  calc s = (s₀ : GL (Fin n ⊕ Fin n) F) := hs₀.symm
    _ = (s₁ : GL (Fin n ⊕ Fin n) F) := by rw [hEq]
    _ = s' := hs₁

end CFSG.StandardType.ClassicalPosition
