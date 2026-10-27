module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_13_1 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    (∃ A : Subgroup G, Choice1613 D V₀ V hV L A) ∧
      ∀ A : Subgroup G, Choice1613 D V₀ V hV L A → ∀ g : G, A ≤ conjSubgroup V g →
        ¬ conjSubgroup V g ≤ D.M ∧ (V ≤ conjSubgroup D.M g → Case168_2 D V₀ V hV L)

@[expose] noncomputable def Concl1613_2 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) : Prop :=
  Case168_2Small D V₀ V hV L ∨ Case168_4With D V₀ V hV L 3 ∨ Case168_3 D V₀ V hV L ∨
    Case168_8 D V₀ V hV ∨ Case168_9 D V₀ V hV L ∨ Case168_10 D V₀ V hV L ∨
    Case168_11 D V₀ V hV L

@[expose] def R16_13_2 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    Concl1613_2 D V₀ V hV L

@[expose] def R16_14 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    (((D.k + 2 : ℕ) : ℕ∞) < rMV D.M V)

@[expose] def R16_15 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    ∀ A : Subgroup G, Choice1613 D V₀ V hV L A →
      2 < rk ↥(barSub V₀ V hV A) ∧
        (Case168_2 D V₀ V hV L ∨ Case168_4At D V₀ V hV L 3 3 ∨ Case168_10At D V₀ V hV L 3 ∨
          Case168_9 D V₀ V hV L)

@[expose] def R16_16 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    ¬ IsLn ↥(lBar V₀ V hV L) 4 1

@[expose] def R16_17 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    ∀ A : Subgroup G, Choice1613 D V₀ V hV L A → ∀ g : G, A ≤ conjSubgroup V g →
      ∃ Δ : Set (Subgroup G), Concl1617 D V₀ V hV L A g Δ

@[expose] def R16_18 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    ∀ (A : Subgroup G) (g : G) (Δ : Set (Subgroup G)), Choice1613 D V₀ V hV L A →
      A ≤ conjSubgroup V g → Concl1617 D V₀ V hV L A g Δ →
        ∀ B U : Subgroup G, Hyperplane1618 V A B U →
          (E3.mQuot (conjSubgroup V g) B = mBar D.M V₀ V hV ∧ mBar D.M V₀ V hV = D.k + 1) ∧
          (B = conjSubgroup V g ⊓ centralizer (U : Set G) ∧
            B = ⨆ I ∈ deltaConj Δ g, I ⊓ centralizer (U : Set G) ∧
            B = ⨆ I ∈ deltaConj Δ g, B ⊓ I) ∧
          (¬ Case168_2 D V₀ V hV L → ∃! J : Subgroup G, J ∈ deltaConj Δ g ∧ J ≤ B) ∧
          (Case168_2 D V₀ V hV L → ∀ J ∈ deltaConj Δ g, E3.mQuot J (B ⊓ J) = 1)

@[expose] def R16_19 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    Case168_2 D V₀ V hV L ∨ Case168_9 D V₀ V hV L

@[expose] def R16_20 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    ∀ (A : Subgroup G) (g : G) (Δ : Set (Subgroup G)), Choice1613 D V₀ V hV L A →
      A ≤ conjSubgroup V g → Concl1617 D V₀ V hV L A g Δ →
        ∀ B U : Subgroup G, Hyperplane1618 V A B U →
          Case168_2 D V₀ V hV L ∧
          (B = A ⊓ preBarSub D.M V₀ V hV
              (centralizer ((oddBar D.M V₀ V hV : Subgroup (MulAut (Vtil V₀ V hV))) :
                Set (MulAut (Vtil V₀ V hV)))) ∧
            ∀ b ∈ B, ∀ I ∈ Δ, conjSubgroup I b = I) ∧
          (∀ I ∈ Δ, Nat.card ↥(I ⊓ centralizer (B : Set G)) = 2) ∧
          barSub V₀ V hV B ∈ calABar 2 D.M V₀ V hV

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
