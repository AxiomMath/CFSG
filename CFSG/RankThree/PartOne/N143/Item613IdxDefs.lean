module

public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

@[expose] def ListEvenItem (X : Type) [Group X] : Prop :=
  Census3.ThmThreeItem7 X ∨ Census3.ThmThreeItem8 X ∨ Census3.ThmThreeItem9 X

theorem ListEvenItem.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : ListEvenItem G) : ListEvenItem H := by
  have key : ∀ {X : Type} [Group X], Nonempty (G ≃* X) → Nonempty (H ≃* X) :=
    fun ⟨f⟩ => ⟨e.symm.trans f⟩
  have iso : ∀ {d : TauCeti.LieTypeIndex}, Census3.IsoLie G d → Census3.IsoLie H d :=
    fun ⟨hv, hf⟩ => ⟨hv, key hf⟩
  have i7 : Census3.ThmThreeItem7 G → Census3.ThmThreeItem7 H :=
    Or.imp (fun ⟨q, a, c⟩ => ⟨q, a, iso c⟩) <| Or.imp (fun ⟨m, c⟩ => ⟨m, iso c⟩) <|
      Or.imp (fun ⟨q, a, c⟩ => ⟨q, a, c.imp iso <| Or.imp iso <| Or.imp iso <| Or.imp iso <|
        Or.imp iso <| Or.imp iso iso⟩) <| Or.imp (fun ⟨m, c⟩ => ⟨m, iso c⟩) iso
  have i8 : Census3.ThmThreeItem8 G → Census3.ThmThreeItem8 H :=
    fun ⟨q, a, c⟩ => ⟨q, a, c.imp iso <| Or.imp iso iso⟩
  have i9 : Census3.ThmThreeItem9 G → Census3.ThmThreeItem9 H :=
    fun ⟨q, a, b, c⟩ => ⟨q, a, b, c.imp iso <| Or.imp iso <| Or.imp iso <| Or.imp iso <|
      Or.imp iso <| Or.imp iso iso⟩
  exact Or.imp i7 (Or.imp i8 i9) h

@[expose] def Item613AtIdx (X : Type) [Group X] : Prop :=
  ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ E : Subgroup X, CFSG.IsElementaryAbelian p E → p ^ 2 ≤ Nat.card E →
    (∃ S : Subgroup X, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set X) ∧ ⁅S, E⁆ = S) →
    ListEvenItem X

@[expose] def Item613IdxFor (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → P X → Item613AtIdx X

end CFSG.RankThree.PartOne.N143
