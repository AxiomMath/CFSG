module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T517.Decomp

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem theorem_5_17 {p : ℕ} (hp : p.Prime) {H B : Subgroup Γ} {θ : Γ → Subgroup Γ}
    (hB : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2) (hBH : B ≤ H) (hsol : sol H = ⊥)
    (hreg₁ : ∀ J ∈ lcal H, ∀ J' ∈ lcal H, ∃ b ∈ B, J' = J.map (MulAut.conj b).toMonoidHom)
    (hreg₂ : ∀ J ∈ lcal H, ∀ b ∈ B, b ≠ 1 → J.map (MulAut.conj b).toMonoidHom ≠ J)
    (hθ : IsFunctor p B θ) (hθH : ∀ b ∈ B, b ≠ 1 → θ b ≤ H)
    (hC : ∀ b ∈ B, b ≠ 1 → signalizerMcBrideHypothesisB p (θ b))
    (h₁ : ∀ b ∈ B, b ≠ 1 → kOf H ⊓ Subgroup.centralizer {b} ≤ θ b)
    (h₂ : ∀ b ∈ B, b ≠ 1 → Nonempty ((Fin p → ↥(thetaOf θ B)) ≃* ↥(θ b))) :
    ∃ W, IsGreatest (Msig p B θ) W ∧
      (∀ J ∈ lcal H, W ⊓ jTilde H J =
        projIn (jTilde H '' lcal H) (jTilde H J) (thetaOf θ B)) ∧
      IsDirectProduct {Y | ∃ J ∈ lcal H, Y = W ⊓ jTilde H J} W := by
  have S : T517.Setting p H B θ :=
    { prime := hp, elemAbelian := hB, card := hBcard, le := hBH, sol_eq_bot := hsol,
      trans := hreg₁, free := hreg₂, functor := hθ, le_H := hθH, hypB := hC,
      kOf_inf_le := h₁, iso := h₂ }
  exact ⟨thetaSup B θ, S.isGreatest_thetaSup, fun _ hJ => S.inf_jTilde_eq_projIn hJ,
    S.isDirectProduct_Y⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
