module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusDatum
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcEndPow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.HardMathSupport.C14Exc

@[expose] def KGLangTorusMPart (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ [Finite (HopfCover R)] (θ : HopfCover R ⧸ Subgroup.center (HopfCover R) ≃* R),
    commutator (HopfCover R) = ⊤ →
    ∀ A : Subgroup (MulAut (HopfCover R)), IsElemAbelian p A →
      (∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f) →
      (∃ α ∈ A, α ≠ 1 ∧ kgInducedAut θ α ∈ I) →
      ∀ α₀ ∈ A, kgInducedAut θ α₀ ∉ I →
        ∃ M : Subgroup (HopfCover R), (∀ a ∈ M, ∀ c ∈ M, a * c = c * a) ∧
          (∀ t, α₀ t ∈ M ↔ t ∈ M) ∧
          (∀ α ∈ A, kgInducedAut θ α ∈ I → ∀ t ∈ M, α t = t) ∧
          (∀ c ∈ M, ((List.range p).map fun i => (α₀ ^ i) c).prod = 1 → ∃ s ∈ M, c = s⁻¹ * α₀ s) ∧
          ∃ e ∈ M, e ≠ 1 ∧ e ^ p = 1 ∧ α₀ e = e

@[expose] def KGLangTorusInput (p : ℕ) {Γ : Type*} [Group Γ] (G : Subgroup Γ) (F₀ : Γ →* Γ) : Prop :=
  ∀ E : Subgroup Γ, IsElemAbelian p E → (∀ x ∈ E, x ∈ G ∧ F₀ x = x) →
    ∃ N : Subgroup Γ, N ≤ G ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ (∀ x ∈ N, F₀ x ∈ N) ∧
      (∀ c ∈ N, ((List.range p).map fun i => endPow F₀ i c).prod = 1 → ∃ s ∈ N, c = s⁻¹ * F₀ s) ∧
      E ≤ N

end CFSG.StandardType
