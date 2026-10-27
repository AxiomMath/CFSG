module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (InCatalog)

@[expose] def FF79_4_2KLor : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G),
    FF79Sec4 b J B b₁ b₂ →
    let β := b₁ * b₂; let γ := b₁ ^ 2 * b₂; let H := OUp 3 (Cen β)
    let K := Lay (H ⊓ Cen b); let L := Lay (H ⊓ Cen γ)
    (Subgroup.zpowers β ⊔ H = Cen β ∧ Subgroup.zpowers β ⊓ H = ⊥) ∧
    IsSylowOf 3 (Subgroup.closure {b, γ}) H ∧ b ∈ L ∧ γ ∈ K ∧
    ((IsLnq 2 2 2 K ∧ IsLnq 3 2 1 L) ∨ (IsLnq 3 2 1 K ∧ IsLnq 2 2 2 L))

@[expose] def FF79LemmaN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Q L : Subgroup G) (b : G),
    KCore.KGroupNonab InCatalog ↥Q → Nonempty (L ≃* GL (Fin 3) (ZMod 2)) →
    L ≤ Nor Q → Nat.Coprime 3 (Nat.card Q) → b ∈ L → orderOf b = 3 →
    Q ⊓ Cen b ≤ CenS L → Q ≤ CenS L

end CFSG.RankThree.PartTwo.Sec21.FF79
