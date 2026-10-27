module

public import Certificates.Certificate709550
public import Certificates.Certificate709551

public section

namespace CFSG.StandardType.ZS

theorem mem_closure_of_b3Chain_of_N4 {p : ℕ} {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} (hone : OneClass p A)
    (hmod : ModelIso p .N4 A) {r₁ r₂ r₃ r₄ t : U ≃ₗ[ZMod p] U} (h₁ : r₁ ∈ A) (h₂ : r₂ ∈ A)
    (h₃ : r₃ ∈ A) (h₄ : r₄ ∈ A) (ht : t ∈ A) (hr₁ : IsRefl p r₁) (hr₂ : IsRefl p r₂)
    (hr₃ : IsRefl p r₃) (hr₄ : IsRefl p r₄) (hrt : IsRefl p t) (h12 : orderOf (r₁ * r₂) = 3)
    (h23 : orderOf (r₂ * r₃) = 4) (h13 : orderOf (r₁ * r₃) = 2)
    (hW : Nat.card (Subgroup.closure {r₁, r₂, r₃, r₄}) = 384)
    (hle : Nat.card (Subgroup.closure {r₁, r₂, r₃, t}) ≤ 384) :
    t ∈ Subgroup.closure {r₁, r₂, r₃, r₄} :=
  Certificates.certificate709550 hone hmod h₁ h₂ h₃ h₄ ht hr₁ hr₂ hr₃ hr₄ hrt h12 h23 h13 hW hle

theorem exists_two_refl_commute_not_mem_of_EN4 {p : ℕ} {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} (hone : OneClass p A)
    (hmod : ModelIso p .EN4 A) {r₁ r₂ r₃ : U ≃ₗ[ZMod p] U} (h₁ : r₁ ∈ A) (h₂ : r₂ ∈ A)
    (h₃ : r₃ ∈ A) (hr₁ : IsRefl p r₁) (hr₂ : IsRefl p r₂) (hr₃ : IsRefl p r₃)
    (h12 : orderOf (r₁ * r₂) = 3) (h23 : orderOf (r₂ * r₃) = 4) (h13 : orderOf (r₁ * r₃) = 2) :
    ∃ s₁ ∈ A, ∃ s₂ ∈ A, s₁ ≠ s₂ ∧ IsRefl p s₁ ∧ IsRefl p s₂ ∧
      Commute s₁ ((r₁ * r₂ * r₃) ^ 3) ∧ Commute s₂ ((r₁ * r₂ * r₃) ^ 3) ∧
      s₁ ∉ Subgroup.closure {r₁, r₂, r₃} ∧ s₂ ∉ Subgroup.closure {r₁, r₂, r₃} :=
  Certificates.certificate709551 hone hmod h₁ h₂ h₃ hr₁ hr₂ hr₃ h12 h23 h13

end CFSG.StandardType.ZS

end
