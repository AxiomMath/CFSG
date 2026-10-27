module

public import CFSG.Quasithin.Background.F1Borel

public section

namespace CFSG.Quasithin.WBN

@[expose] def WBNInversionL2 : Prop :=
  ∀ (G₀ : Type) [Group G₀] [Finite G₀] (L₁ L₂ S : Subgroup G₀) (f₁ f₂ : ℕ),
    CFSG.Quasithin.Hyp111 L₁ L₂ S →
    (S.subgroupOf (S ⊔ CFSG.Quasithin.borelOf L₂ S)).Normal →
    2 ≤ f₁ →
    (Nonempty (CFSG.Quasithin.oTwoQuot ↥L₁ ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f₁)) ∨
      ∃ a : ℕ, f₁ = 2 * a + 1 ∧ Nonempty (CFSG.Quasithin.oTwoQuot ↥L₁ ≃* ↥(CFSG.Open.Sz a))) →
    2 ≤ f₂ →
    Nonempty (CFSG.Quasithin.oTwoQuot ↥L₂ ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f₂)) →
    (∀ E : Subgroup G₀, E ≤ CFSG.Quasithin.bigB L₁ L₂ S →
        (∀ e ∈ E, e ^ (2 ^ f₁ - 1) = 1 ∧ e ^ (2 ^ f₂ - 1) = 1) →
        ∃ w ∈ L₁ ⊔ L₂ ⊔ S, ∀ e ∈ E, w * e * w⁻¹ = e⁻¹) ∨
      CFSG.Open.pCoreOf 2 (L₁ ⊔ CFSG.Quasithin.bigB L₁ L₂ S) ⊓
          Subgroup.centralizer (L₁ : Set G₀) = ⊥

end CFSG.Quasithin.WBN

end
