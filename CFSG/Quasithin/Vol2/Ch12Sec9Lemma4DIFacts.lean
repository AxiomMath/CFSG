module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I]

@[expose] def stabS (S : Submodule (ZMod 2) I) : Subgroup (I ≃ₗ[ZMod 2] I) where
  carrier := {g | ∀ v, v ∈ S ↔ g v ∈ S}
  mul_mem' := fun {a b} ha hb v => (hb v).trans (ha (b v))
  one_mem' := fun _ => Iff.rfl
  inv_mem' := fun {a} ha v => by
    have h := ha (a⁻¹ v)
    have e : a (a⁻¹ v) = v := a.apply_symm_apply v
    rw [e] at h
    exact h.symm

@[expose] def FactF0 : Prop :=
  ∀ (I : Type) [AddCommGroup I] [Module (ZMod 2) I], Module.finrank (ZMod 2) I = 4 →
    ∀ c : I →ₗ[ZMod 2] I, (∀ g : I ≃ₗ[ZMod 2] I, ∀ v, c (g v) = g (c v)) →
      c = 0 ∨ c = LinearMap.id

@[expose] def FactF1 : Prop :=
  (∀ (I : Type) [AddCommGroup I] [Module (ZMod 2) I] [Finite I],
    Module.finrank (ZMod 2) I = 4 → ∀ B₀ : Subgroup (I ≃ₗ[ZMod 2] I),
      IsPGroup 2 B₀ → ¬ 2 ∣ B₀.index →
      ∃ p ℓ Pl : Submodule (ZMod 2) I, Module.finrank (ZMod 2) p = 1 ∧
        Module.finrank (ZMod 2) ℓ = 2 ∧ Module.finrank (ZMod 2) Pl = 3 ∧ p < ℓ ∧ ℓ < Pl ∧
        B₀ = stabS p ⊓ stabS ℓ ⊓ stabS Pl) ∧
  (∀ (I : Type) [AddCommGroup I] [Module (ZMod 2) I] [Finite I],
    Module.finrank (ZMod 2) I = 4 → ∀ p ℓ Pl : Submodule (ZMod 2) I,
      Module.finrank (ZMod 2) p = 1 → Module.finrank (ZMod 2) ℓ = 2 →
      Module.finrank (ZMod 2) Pl = 3 → p < ℓ → ℓ < Pl →
      (stabS ℓ).index = 35 ∧ (stabS p).index = 15 ∧ (stabS Pl).index = 15 ∧
      (stabS p ⊓ stabS ℓ).index = 105 ∧ (stabS p ⊓ stabS Pl).index = 105 ∧
      (stabS ℓ ⊓ stabS Pl).index = 105 ∧ (stabS p ⊓ stabS ℓ ⊓ stabS Pl).index = 315 ∧
      ∀ X : Subgroup (I ≃ₗ[ZMod 2] I), stabS p ⊓ stabS ℓ ⊓ stabS Pl ≤ X →
        X = ⊤ ∨ X = stabS p ∨ X = stabS ℓ ∨ X = stabS Pl ∨ X = stabS p ⊓ stabS ℓ ∨
          X = stabS p ⊓ stabS Pl ∨ X = stabS ℓ ⊓ stabS Pl ∨ X = stabS p ⊓ stabS ℓ ⊓ stabS Pl)

@[expose] def D0p (p ℓ : Submodule (ZMod 2) I) : Subgroup (I ≃ₗ[ZMod 2] I) :=
  pCoreOf 2 (stabS p) ⊓ pCoreOf 2 (stabS ℓ)

@[expose] def D0P (ℓ Pl : Submodule (ZMod 2) I) : Subgroup (I ≃ₗ[ZMod 2] I) :=
  pCoreOf 2 (stabS Pl) ⊓ pCoreOf 2 (stabS ℓ)

@[expose] def FactF2 : Prop :=
  ∀ (I : Type) [AddCommGroup I] [Module (ZMod 2) I] [Finite I],
    Module.finrank (ZMod 2) I = 4 → ∀ p ℓ Pl : Submodule (ZMod 2) I,
      Module.finrank (ZMod 2) p = 1 → Module.finrank (ZMod 2) ℓ = 2 →
      Module.finrank (ZMod 2) Pl = 3 → p < ℓ → ℓ < Pl →
      (Nat.card (D0p p ℓ) = 4 ∧ (∀ d ∈ D0p p ℓ, d ^ 2 = 1) ∧
        ∀ v : I, (∀ d ∈ D0p p ℓ, d v = v) ↔ v ∈ ℓ) ∧
      (Nat.card (D0P ℓ Pl) = 4 ∧ (∀ d ∈ D0P ℓ Pl, d ^ 2 = 1) ∧
        ∀ v : I, (∀ d ∈ D0P ℓ Pl, d v = v) ↔ v ∈ Pl)

@[expose] def FactF3 : Prop :=
  ∀ (I : Type) [AddCommGroup I] [Module (ZMod 2) I] [Finite I],
    Module.finrank (ZMod 2) I = 4 → ∀ p ℓ Pl : Submodule (ZMod 2) I,
      Module.finrank (ZMod 2) p = 1 → Module.finrank (ZMod 2) ℓ = 2 →
      Module.finrank (ZMod 2) Pl = 3 → p < ℓ → ℓ < Pl →
      ∀ g : I ≃ₗ[ZMod 2] I, orderOf g = 3 →
        (g ∈ stabS p → g ∈ stabS ℓ →
          (∀ v ∈ ℓ, g v = v) ∧ (∀ v : I, g v - v ∈ ℓ → v ∈ ℓ) ∧
          (∀ d ∈ D0p p ℓ, g * d * g⁻¹ = d → d = 1)) ∧
        (g ∈ stabS ℓ → g ∈ stabS Pl → ∀ d ∈ D0P ℓ Pl, g * d * g⁻¹ = d → d = 1)

@[expose] def FactF4 : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (q : W → ZMod 2)
    (B : LinearMap.BilinForm (ZMod 2) W),
    Module.finrank (ZMod 2) W = 6 → (∀ v w, q (v + w) = q v + q w + B v w) →
    (∀ v, (∀ w, B v w = 0) → v = 0) →
    (∃ S : Submodule (ZMod 2) W, Module.finrank (ZMod 2) S = 3 ∧ ∀ s ∈ S, q s = 0) →
    Nat.card (orthogonalSubgroupOf q) = 40320 ∧
    (∀ N : Subgroup (W ≃ₗ[ZMod 2] W), N ≤ orthogonalSubgroupOf q →
      (∀ γ ∈ orthogonalSubgroupOf q, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → Nat.card N ≠ 2) ∧
    ∀ Ω : Subgroup (W ≃ₗ[ZMod 2] W), Ω ≤ orthogonalSubgroupOf q →
      Ω.relIndex (orthogonalSubgroupOf q) = 2 →
      (∀ v w : W, v ≠ 0 → w ≠ 0 → q v = 0 → q w = 0 → ∃ γ ∈ Ω, γ v = w) ∧
      (∀ v : W, v ≠ 0 → q v = 0 → (stabS (Submodule.span (ZMod 2) {v})).relIndex Ω = 35) ∧
      (∀ S : Submodule (ZMod 2) W, Module.finrank (ZMod 2) S = 3 → (∀ s ∈ S, q s = 0) →
        (∀ γ ∈ orthogonalSubgroupOf q, (∀ v, v ∈ S ↔ γ v ∈ S) → γ ∈ Ω) ∧
        (stabS S).relIndex Ω = 15 ∧
        Nat.card (pCoreOf 2 (stabS S ⊓ Ω)) = 8 ∧
        ∀ γ ∈ stabS S ⊓ Ω, (∀ s ∈ S, γ s = s) ↔ γ ∈ pCoreOf 2 (stabS S ⊓ Ω)) ∧
      (∀ w : W, w ≠ 0 → q w = 0 →
        Nat.card (pCoreOf 2 (stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω)) = 16 ∧
        ∀ γ ∈ stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω,
          (∀ x : W, B x w = 0 → γ x - x ∈ Submodule.span (ZMod 2) {w}) ↔
            γ ∈ pCoreOf 2 (stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω))

end CFSG.Quasithin.H13.C1294
