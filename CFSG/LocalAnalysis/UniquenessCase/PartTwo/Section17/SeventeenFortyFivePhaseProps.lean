module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open scoped Pointwise commutatorElement

@[expose] def SmallWeylIndex45 : TauCeti.LieTypeIndex → Prop
  | .A r _ => r ≤ 3
  | .twistedA r _ => r ≤ 3
  | .B r _ => r ≤ 4
  | .C r _ => r ≤ 4
  | .D r _ => r ≤ 4
  | .twistedD r _ => r ≤ 4
  | .G2 _ => True
  | .F4 _ => True
  | .trialityD4 _ => True
  | _ => False

@[expose] def BigNonLinIndex45 : TauCeti.LieTypeIndex → Prop
  | .B r _ => 5 ≤ r
  | .C r _ => 5 ≤ r
  | .D r _ => 5 ≤ r
  | .twistedD r _ => 5 ≤ r
  | .E6 _ => True
  | .E7 _ => True
  | .E8 _ => True
  | .twistedE6 _ => True
  | _ => False

@[expose] def RankOneIndex45 (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d = .A 1 q ∨ d = .twistedA 2 q

structure PhaseConfig45 {X : Type} [Group X] [Finite X] (L A₁ A₂ B T ML : Subgroup X) : Prop where
  hLn : L.Normal
  hLs : IsSimpleGroup L
  hLnab : ¬ IsMulCommutative L
  hLK : CFSG.Open.IsKGroup L
  hCL : centralizer (L : Set X) = ⊥
  hA1 : Nat.card A₁ = 31
  hA2 : Nat.card A₂ = 31
  hA12 : A₁ ⊓ A₂ = ⊥
  hA12c : A₁ ≤ centralizer (A₂ : Set X)
  hB5 : Nat.card B = 5
  hBA1 : B ≤ normalizer (A₁ : Set X)
  hBA2 : B ≤ normalizer (A₂ : Set X)
  hcomm : ⁅A₁ ⊔ A₂, B⁆ = A₁ ⊔ A₂
  hlines : ∀ D : Subgroup X, D ≤ A₁ ⊔ A₂ → Nat.card D = 31 → B ≤ normalizer (D : Set X) →
    D = A₁ ∨ D = A₂
  hT : IsPGroup 2 T
  hAT : ((A₁ ⊔ A₂ : Subgroup X) : Set X) * (T : Set X) =
    (T : Set X) * ((A₁ ⊔ A₂ : Subgroup X) : Set X)
  hBT : (B : Set X) * (T : Set X) = (T : Set X) * (B : Set X)
  hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L
  hML : ML ≤ L
  hMLne : ML ≠ L
  hTML : T ⊓ L ≤ ML
  hC5 : ∀ C : Subgroup X, IsMulCommutative C → (A₁ ≤ C ∨ A₂ ≤ C ∨ B ≤ C) →
    L ⊓ normalizer (C : Set X) ≤ ML
  hC6 : 5 ∣ Nat.card L → CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 (ML.subgroupOf L)

@[expose] def K45CharTwoNormal : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L A₁ A₂ B T : Subgroup X) (d : TauCeti.ValidLieTypeIndex),
    L.Normal → centralizer (L : Set X) = ⊥ →
    Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    d.1.characteristic = 2 → d.1 ≠ .tits →
    Nat.card A₁ = 31 → Nat.card A₂ = 31 → A₁ ⊓ A₂ = ⊥ → A₁ ≤ centralizer (A₂ : Set X) →
    Nat.card B = 5 → B ≤ normalizer (A₁ : Set X) → B ≤ normalizer (A₂ : Set X) →
    ⁅A₁ ⊔ A₂, B⁆ = A₁ ⊔ A₂ → IsPGroup 2 T →
    ((A₁ ⊔ A₂ : Subgroup X) : Set X) * (T : Set X) =
      (T : Set X) * ((A₁ ⊔ A₂ : Subgroup X) : Set X) →
    CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L →
    A₁ ⊔ A₂ ≤ normalizer ((T ⊓ L : Subgroup X) : Set X)

@[expose] def K45CharTwoBorelGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L A₁ A₂ B S : Subgroup X) (d : TauCeti.ValidLieTypeIndex),
    L.Normal → centralizer (L : Set X) = ⊥ →
    Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    d.1.characteristic = 2 → d.1 ≠ .tits →
    Nat.card A₁ = 31 → Nat.card A₂ = 31 → A₁ ⊓ A₂ = ⊥ → A₁ ≤ centralizer (A₂ : Set X) →
    Nat.card B = 5 → B ≤ normalizer (A₁ : Set X) → B ≤ normalizer (A₂ : Set X) →
    ⁅A₁ ⊔ A₂, B⁆ = A₁ ⊔ A₂ →
    CFSG.ABGLocalTools.IsSylowOf 2 S L → A₁ ⊔ A₂ ≤ normalizer (S : Set X) →
    ∃ C : Subgroup X, IsMulCommutative C ∧ A₁ ≤ C ∧ L ≤ S ⊔ (L ⊓ normalizer (C : Set X))

@[expose] def K45WeylFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L A₁ A₂ B : Subgroup X) (d : TauCeti.ValidLieTypeIndex),
    L.Normal → centralizer (L : Set X) = ⊥ →
    Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    SmallWeylIndex45 d.1 → d.1.characteristic ≠ 2 → d.1.characteristic ≠ 31 →
    Nat.card A₁ = 31 → Nat.card A₂ = 31 → A₁ ⊓ A₂ = ⊥ → A₁ ≤ centralizer (A₂ : Set X) →
    Nat.card B = 5 → B ≤ normalizer (A₁ : Set X) → B ≤ normalizer (A₂ : Set X) →
    ⁅A₁ ⊔ A₂, B⁆ = A₁ ⊔ A₂ →
    (∀ D : Subgroup X, D ≤ A₁ ⊔ A₂ → Nat.card D = 31 → B ≤ normalizer (D : Set X) →
      D = A₁ ∨ D = A₂) →
    False

@[expose] def K45FiveRankTwo : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    d.1.characteristic ≠ 2 → d.1.characteristic ≠ 5 →
    (BigNonLinIndex45 d.1 ∨
      (d.1.characteristic = 31 ∧ SmallWeylIndex45 d.1 ∧ ¬ RankOneIndex45 d.1)) →
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K)

@[expose] def K45UnitaryThirtyOneGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L A₁ T : Subgroup X) (d : TauCeti.ValidLieTypeIndex),
    Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    (∃ q : TauCeti.PrimePower, q.p = 31 ∧ d.1 = .twistedA 2 q) →
    A₁ ≤ L → Nat.card A₁ = 31 → CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L →
    ∃ C : Subgroup X, IsMulCommutative C ∧ A₁ ≤ C ∧
      L ≤ (T ⊓ L) ⊔ (L ⊓ normalizer (C : Set X))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
