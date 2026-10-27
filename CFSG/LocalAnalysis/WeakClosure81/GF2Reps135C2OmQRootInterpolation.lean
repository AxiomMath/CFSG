module

public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

@[expose] def OmqRootInterpolation : Prop :=
  ∀ {G : Type} [Group G] (H : Subgroup G)
    {F k V : Type} [Field F] [Fintype F] [Field k] [AddCommGroup V] [Module k V]
    (ι : F →+* k) (ρ : Representation k G V) (X Y : F → G)
    (v₀ : V) (φ : Module.Dual k V) (χ : H →* kˣ) (α : H →* Fˣ)
    {c : ℕ} (hc : c < Fintype.card F)
    (hweight : ∀ h : H, ρ (h : G) v₀ = (χ h : k) • v₀)
    (hconj : ∀ (h : H) (t : F),
      (h : G) * Y t * (h : G)⁻¹ = Y ((α h : F)⁻¹ * t))
    (hcoeff : ∀ s t : F,
      φ (ρ (X s * Y t) v₀) = (1 + ι s * ι t) ^ c),
    ∃ w : Fin (Fintype.card F) → V,
      (∀ t : F, ρ (Y t) v₀ = ∑ j, (ι t) ^ j.val • w j) ∧
      (∀ (j : Fin (Fintype.card F)) (s : F),
        φ (ρ (X s) (w j)) = (Nat.choose c j.val : k) * (ι s) ^ j.val) ∧
      (∀ (j : Fin (Fintype.card F)) (h : H),
        ρ (h : G) (w j) = ((χ h : k) * (ι (α h : F))⁻¹ ^ j.val) • w j) ∧
      (∀ j : Fin (Fintype.card F), (Nat.choose c j.val : k) ≠ 0 → w j ≠ 0)

end CFSG.LocalAnalysis.WeakClosure81
