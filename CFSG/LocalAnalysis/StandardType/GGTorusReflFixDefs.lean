module

public import CFSG.LocalAnalysis.StandardType.GGKGForkTransfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGKGReflFix (p s : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E H : Subgroup R, IsElemAbelian p E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → H ≤ E → p ^ s ≤ Nat.card H →
    (∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) →
    ∃ w : R, GGKGIsReflAt p E w ∧ ∀ h ∈ H, w * h = h * w

@[expose] def GGTorusReflFix (p r s : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A → ∀ H : Subgroup (MulAut L'), H ≤ A → p ^ s ≤ Nat.card H →
    (∃ V : Subgroup R, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ h ∈ H, ∀ l : L', ψ l ∈ V → ψ (h l) ∈ V) →
    ∃ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p φ ∧
      ∀ (h : MulAut L') (ha : h ∈ A), h ∈ H → φ ⟨h, ha⟩ = ⟨h, ha⟩

end CFSG.StandardType

end
