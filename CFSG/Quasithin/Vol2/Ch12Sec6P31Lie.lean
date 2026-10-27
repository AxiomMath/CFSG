module

public import CFSG.Quasithin.Vol2.Ch12Sec6Final

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank S126

structure L34Facts12631 {Q : Type*} [Group Q] [Finite Q] (X : Subgroup Q) : Prop where
  three_rank : ∃ A B : Subgroup Q, A ≤ X ∧ B ≤ X ∧ Nat.card A = 3 ∧ Nat.card B = 3 ∧
    A ≤ Subgroup.centralizer (B : Set Q) ∧ A ⊓ B = ⊥
  card_aut : Nat.card (MulAut ↥X) = 241920
  normal_index_four : ∃ P : Subgroup (MulAut ↥X), P.Normal ∧ P.index = 4 ∧
    (MulAut.conj : ↥X →* MulAut ↥X).range ≤ P
  card_borel : ∀ S : Subgroup Q, IsSylowTwoOf S X →
    Nat.card ↥(X ⊓ Subgroup.normalizer (S : Set Q)) = 192
  overgroup : ∀ S N W : Subgroup Q, IsSylowTwoOf S X → X ⊓ Subgroup.normalizer (S : Set Q) ≤ N →
    N ≤ X → N ≠ X ⊓ Subgroup.normalizer (S : Set Q) → N ≠ X → W ≤ N → (W.subgroupOf N).Normal →
    (∀ p : ℕ, p.Prime → p ∣ Nat.card W → p = 2 ∨ p = 3) → ¬ 3 ∣ Nat.card W

structure SL34Facts12631 {Q : Type*} [Group Q] [Finite Q] (X : Subgroup Q) : Prop where
  three_rank : ∃ A B : Subgroup Q, A ≤ X ∧ B ≤ X ∧ Nat.card A = 3 ∧ Nat.card B = 3 ∧
    A ≤ Subgroup.centralizer (B : Set Q) ∧ A ⊓ B = ⊥
  card_aut : Nat.card (MulAut ↥X) ∣ 241920
  out_exp : ∀ α : MulAut ↥X, α ^ 4 ∈ (MulAut.conj : ↥X →* MulAut ↥X).range →
    α ^ 2 ∈ (MulAut.conj : ↥X →* MulAut ↥X).range
  card_borel : ∀ S : Subgroup Q, IsSylowTwoOf S X →
    Nat.card ↥(X ⊓ Subgroup.normalizer (S : Set Q)) = 576
  overgroup : ∀ S N W : Subgroup Q, IsSylowTwoOf S X → X ⊓ Subgroup.normalizer (S : Set Q) ≤ N →
    N ≤ X → N ≠ X ⊓ Subgroup.normalizer (S : Set Q) → N ≠ X → W ≤ N → (W.subgroupOf N).Normal →
    (∀ p : ℕ, p.Prime → p ∣ Nat.card W → p = 2 ∨ p = 3) → ¬ 9 ∣ Nat.card W

@[expose] def L34LieFacts12631 : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 4 → ∀ (Q : Type) [Group Q] [Finite Q]
    (X : Subgroup Q), (Nonempty (↥X ≃* PSL3Model F) → L34Facts12631 X) ∧
      (Nonempty (↥X ≃* ↥(StatedSL 3 F)) → SL34Facts12631 X)

end CFSG.Quasithin.H13
