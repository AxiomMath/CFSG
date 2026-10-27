module

public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.RankThree.GF2n.Tim79Heis

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

section Pairs

variable {K : Type} [Field K] {ι : Type}

@[expose] def PairTypeA (q : QuadraticForm K (ι → K)) (p : (ι → K) × (ι → K)) : Prop :=
  ∃ (c₁ c₂ : K) (u : ι → K), (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ u ≠ 0 ∧ q u = 0 ∧ p = (c₁ • u, c₂ • u)

@[expose] def orthTensor (g : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) → (ι → K))
    (p : (ι → K) × (ι → K)) : (ι → K) × (ι → K) :=
  (g 0 0 • o p.1 + g 0 1 • o p.2, g 1 0 • o p.1 + g 1 1 • o p.2)

end Pairs

section Coordinates

variable {G : Type} [Group G]

structure OrthFrame (Q Z : Subgroup G) {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (qU : QuadraticForm K (ι → K)) (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)) : Prop where
  nondeg : ∀ u : ι → K, (∀ v : ι → K, QuadraticMap.polar qU u v = 0) → u = 0
  qf : ∀ e : M₀.E, M₀.Qf e = QuadraticMap.polar qU (φ e).1 (φ e).2
  root : ∀ z ∈ Z, z ≠ 1 → ∀ x ∈ Q, x ∉ Z → (IsConj z x ↔ PairTypeA qU (φ (M₀.π x)))

end Coordinates

end CFSG.RankThree.GF2n.Smith81
