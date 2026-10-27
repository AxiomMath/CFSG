module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

@[expose] def FF79_4_2Pre : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G),
    FF79Sec4 b J B b₁ b₂ →
    let β := b₁ * b₂; let γ := b₁ ^ 2 * b₂; let H := OUp 3 (Cen β)
    let K := Lay (H ⊓ Cen b); let L := Lay (H ⊓ Cen γ)
    (Subgroup.zpowers β ⊔ H = Cen β ∧ Subgroup.zpowers β ⊓ H = ⊥) ∧
    IsSylowOf 3 (Subgroup.closure {b, γ}) H ∧
    IsLnq 2 2 2 K ∧ IsLnq 3 2 1 L ∧ b ∈ L ∧ γ ∈ K ∧
    Lay H = K ⊔ L ∧ K ⊓ L = ⊥ ∧ K ≤ CenS L ∧
    (setMul (H ⊓ CenS (Subgroup.closure {b, γ})) (Lay H) = H) ∧
    Opp 3 H = Opp 3 (Cen b) ∧ Opp 3 (Cen b) ≤ Opp 3 (CenS B)

end CFSG.RankThree.PartTwo.Sec21.FF79
