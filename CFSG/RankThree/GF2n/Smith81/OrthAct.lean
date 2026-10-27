module

public import CFSG.RankThree.GF2n.Smith81.OrthModel
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {G : Type} [Group G]

section Defs

variable (Q Z : Subgroup G) {K : Type} [Field K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
  {ι : Type} [Fintype ι] [DecidableEq ι] (qU : QuadraticForm K (ι → K))
  (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K))

structure OrthPreFrame : Prop where
  nondeg : ∀ u : ι → K, (∀ v : ι → K, QuadraticMap.polar qU u v = 0) → u = 0
  qf : ∀ e : M₀.E, M₀.Qf e = QuadraticMap.polar qU (φ e).1 (φ e).2

@[expose] def ActsAsTensor (s : G) (g : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) → (ι → K)) : Prop :=
  ∀ x ∈ Q, φ (M₀.π (s * x * s⁻¹)) = orthTensor g o (φ (M₀.π x))

structure OrthAct (S : Subgroup G) : Prop where
  act : ∀ s ∈ S, ∃ (g : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) ≃ₗ[K] (ι → K)), g.det = 1 ∧
    (∀ v, qU (o v) = qU v) ∧ ActsAsTensor Q Z M₀ φ s g o
  sl : ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 → ∃ s ∈ S, ActsAsTensor Q Z M₀ φ s g id
  eich : ∀ a w : ι → K, qU a = 0 → QuadraticMap.polar qU a w = 0 →
    ∃ s ∈ S, ActsAsTensor Q Z M₀ φ s 1 (eichler qU a w)

end Defs

theorem OrthFrame.toPreFrame {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {qU : QuadraticForm K (ι → K)} {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}
    (h : OrthFrame Q Z M₀ qU φ) : OrthPreFrame Q Z M₀ qU φ :=
  ⟨h.nondeg, h.qf⟩

end CFSG.RankThree.GF2n.Smith81
