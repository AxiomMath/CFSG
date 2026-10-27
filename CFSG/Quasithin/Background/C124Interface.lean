module

public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def Spec4bL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseL2 hV L m → ∃ Ys, StarL2 X V L R hV Ys

@[expose] def Spec4bAlt5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseAlt5 hV L m → ∃ Ys, StarZ3 X V L R hV Ys

@[expose] def Spec4bAlt6b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseAlt6 hV L m → R ≤ L ⊔ (X ⊓ Subgroup.centralizer (V : Set G)) →
      ∃ Ys, StarL2 X V L R hV Ys

@[expose] def Spec4bAlt6c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseAlt6 hV L m → Nat.card ↥(autOn R V) = 2 →
      ∃ Ys, StarZ3 X V L R hV Ys

@[expose] def Spec4bAlt7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseAlt7 hV L m → ∃ Ys, StarZ3 X V L R hV Ys

@[expose] def Spec4bHat6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseHat6 hV L m → ∃ Ys, StarL2 X V L R hV Ys

@[expose] def Spec4bA7Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseA7Four hV L m → ∃ Ys, StarL2 X V L R hV Ys

@[expose] def Spec4cL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseL2 hV L m → BlockData V L → IsLin2Type L 2

@[expose] def Spec4cAlt5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseAlt5 hV L m → BlockData V L → IsAltType L 5

@[expose] def Spec4cAlt6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseAlt6 hV L m → BlockData V L → IsAltBlockType L 6

@[expose] def Spec4cAlt7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseAlt7 hV L m → BlockData V L → IsAltType L 7

@[expose] def Spec4cHat6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseHat6 hV L m → BlockData V L → IsHatA6Block L

@[expose] def Spec4cA7Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
    Entry X T V L R m hV → CaseA7Four hV L m → BlockData V L → IsExcA7Block L

end CFSG.Quasithin.C124
