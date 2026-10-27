module

public import Certificates.Kernel.B3MK.Glue

public section

namespace Certificates

open CFSG.StandardType.ZS in
theorem certificate709551 : ∀ {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)},
    OneClass p A → ModelIso p .EN4 A → ∀ {r₁ r₂ r₃ : U ≃ₗ[ZMod p] U}, r₁ ∈ A → r₂ ∈ A → r₃ ∈ A →
    CFSG.StandardType.ZS.IsRefl p r₁ → CFSG.StandardType.ZS.IsRefl p r₂ → CFSG.StandardType.ZS.IsRefl p r₃ → orderOf (r₁ * r₂) = 3 → orderOf (r₂ * r₃) = 4 →
    orderOf (r₁ * r₃) = 2 →
    ∃ s₁ ∈ A, ∃ s₂ ∈ A, s₁ ≠ s₂ ∧ CFSG.StandardType.ZS.IsRefl p s₁ ∧ CFSG.StandardType.ZS.IsRefl p s₂ ∧
      Commute s₁ ((r₁ * r₂ * r₃) ^ 3) ∧ Commute s₂ ((r₁ * r₂ * r₃) ^ 3) ∧
      s₁ ∉ Subgroup.closure {r₁, r₂, r₃} ∧ s₂ ∉ Subgroup.closure {r₁, r₂, r₃} :=
  CFSG.StandardType.ZS.B3MK.b3_en4

end Certificates
