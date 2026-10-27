module

public import Certificates.Kernel.B3MK.Glue

public section

namespace Certificates

open CFSG.StandardType.ZS in
theorem certificate709550 : ∀ {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)},
    OneClass p A → ModelIso p .N4 A → ∀ {r₁ r₂ r₃ r₄ t : U ≃ₗ[ZMod p] U}, r₁ ∈ A → r₂ ∈ A → r₃ ∈ A → r₄ ∈ A →
    t ∈ A → CFSG.StandardType.ZS.IsRefl p r₁ → CFSG.StandardType.ZS.IsRefl p r₂ → CFSG.StandardType.ZS.IsRefl p r₃ → CFSG.StandardType.ZS.IsRefl p r₄ → CFSG.StandardType.ZS.IsRefl p t →
    orderOf (r₁ * r₂) = 3 → orderOf (r₂ * r₃) = 4 → orderOf (r₁ * r₃) = 2 →
    Nat.card (Subgroup.closure {r₁, r₂, r₃, r₄}) = 384 → Nat.card (Subgroup.closure {r₁, r₂, r₃, t}) ≤ 384 →
    t ∈ Subgroup.closure {r₁, r₂, r₃, r₄} :=
  CFSG.StandardType.ZS.B3MK.b3_n4

end Certificates
