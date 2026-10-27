module

public import CFSG.Quasithin.H13.AS91Sec5ResFacts

public section

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open scoped Pointwise symmDiff

abbrev sextStab : Subgroup S24 := M24g ⊓ MulAction.stabilizer S24 (sextFin 0)

theorem sextStab_le : sextStab ≤ AutPerm := inf_le_left

@[expose] def IsRightCocycle (Γ : Subgroup S24) (hΓ : Γ ≤ AutPerm) (D : ↥Γ → W11) : Prop :=
  ∀ s t : ↥Γ, D (s * t) = (rho11 Γ hΓ t)⁻¹ (D s) * D t

@[expose] noncomputable def coboundary (Γ : Subgroup S24) (hΓ : Γ ≤ AutPerm) (w : W11) :
    ↥Γ → W11 :=
  fun s => (rho11 Γ hΓ s)⁻¹ w * w⁻¹

@[expose] noncomputable def dBeta (Γ : Subgroup S24) : ↥Γ → W11 :=
  fun s => setClass (({0} : Finset (Fin 24)) ∆ {((s : S24)⁻¹) 0})

@[expose] def SextStabAutInner : Prop :=
  ∀ θ : ↥sextStab ≃* ↥sextStab, ∃ n : ↥sextStab, ∀ g : ↥sextStab, θ g = n * g * n⁻¹

@[expose] def SextStabOffender : Prop :=
  ∀ B : Subgroup ↥sextStab, B.Normal → IsPGroup 2 B → B ≠ ⊥ →
    Nat.card {w : W11 // ∀ b ∈ B, rho11 sextStab sextStab_le b w = w} * Nat.card B < 2 ^ 11

@[expose] def SextStabEndScalar : Prop :=
  ∀ f : W11 ≃* W11,
    (∀ (s : ↥sextStab) (w : W11),
      f (rho11 sextStab sextStab_le s w) = rho11 sextStab sextStab_le s (f w)) →
    ∀ w, f w = w

@[expose] def SextStabCocycle : Prop :=
  ∀ D : ↥sextStab → W11, IsRightCocycle sextStab sextStab_le D →
    ∀ χ : ↥sextStab →* Multiplicative (ZMod 2), χ ≠ 1 →
      ∃ (w : W11) (a b : Bool), ∀ s : ↥sextStab,
        D s = coboundary sextStab sextStab_le w s *
          (if a then (if χ s = 1 then 1 else sextClass (sextFin 0)) else 1) *
          (if b then dBeta sextStab s else 1)

end CFSG.Quasithin.H13.AS91.M24G
