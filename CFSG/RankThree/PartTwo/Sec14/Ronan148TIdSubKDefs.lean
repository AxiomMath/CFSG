module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3IdentDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

@[expose] def SubL3Ident148 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P : Subgroup (MulAut X)) (K₀ : Subgroup X) (p f₁ : ℕ)
    [Fact p.Prime], 1 ≤ f₁ → p ≠ 3 → (p = 2 ∨ f₁ ≤ 2) → IsLThreeEpsAt ↥K₀ p f₁ →
    IsSimpleGroup ↥K₀ → CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = 9 →
    (∀ σ ∈ P, ∀ k ∈ K₀, σ k ∈ K₀) → (∀ σ ∈ P, (∀ k ∈ K₀, σ k = k) → σ = 1) →
    (∀ σ ∈ P, σ ≠ 1 → ∀ k ∈ K₀, σ k = k → k ^ p = 1 → k = 1) →
    Ronan148B.L3Ident148 P K₀

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
