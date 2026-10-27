module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts21

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

structure Flag24 {G : Type} [Group G] (L V X T V₁ V₂ : Subgroup G) (n : ℕ) : Prop where
  elem : IsElemAbelian 2 V
  two_le : 2 ≤ n
  le_normalizer : L ≤ Subgroup.normalizer (V : Set G)
  commutator_eq : ⁅V, L⁆ = V
  nat : NatModuleOf L V n
  kind : KindSL3 L V n ∨ KindSp4 L V n
  cL_two : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G))
  le_X : L ≤ X
  normalizer_le : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G)
  sylow : QuasithinUnique.IsSylowTwoOf T (L ⊔ T)
  T_le_V : T ≤ Subgroup.normalizer (V : Set G)
  T_le_L : T ≤ Subgroup.normalizer (L : Set G)
  cV_le : V ⊓ Subgroup.centralizer (L : Set G) ≤ V₁
  le₁₂ : V₁ ≤ V₂
  le₂ : V₂ ≤ V
  stable₁ : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) V₁
  stable₂ : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) V₂
  index₁ : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V₁ = 2 ^ n
  index₂ : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V₂ = 2 ^ (n * 2)
  T_le_V₁ : T ≤ Subgroup.normalizer (V₁ : Set G)
  T_le_V₂ : T ≤ Subgroup.normalizer (V₂ : Set G)

@[expose] def FactRootPoint : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ : Subgroup G) (n : ℕ),
    Flag24 L V X T V₁ V₂ n →
    ∀ E : Subgroup G, E ≤ X ⊓ Subgroup.normalizer (V : Set G) → IsElemAbelian 2 E →
      E3.mQuot V (V ⊓ Subgroup.centralizer (E : Set G)) = n →
      E3.mQuot E (E ⊓ Subgroup.centralizer (V : Set G)) = n →
      Nat.card ↥⁅V, E⁆ ≤ 2 ^ n * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) →
        V ⊓ Subgroup.centralizer (L : Set G) ≤ ⁅V, E⁆ ∧
        IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) ⁅V, E⁆ ∧
        (V ⊓ Subgroup.centralizer (L : Set G)).relIndex ⁅V, E⁆ = 2 ^ n

@[expose] def FactPointTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ : Subgroup G) (n : ℕ),
    Flag24 L V X T V₁ V₂ n → ∀ U : Subgroup G,
      V ⊓ Subgroup.centralizer (L : Set G) ≤ U → U ≤ V →
      IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U →
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ n →
        ∃ l ∈ L, conjSubgroup U l = V₁

@[expose] def FactR2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ : Subgroup G) (n : ℕ)
    (h : Flag24 L V X T V₁ V₂ n), ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      autI h.elem A ∈ E3.aSet n (autI h.elem X) → ¬ A ≤ pCoreOf 2 (LOf L V₂ ⊔ T) →
        ⁅V₂, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V₁ ∧
        E3.mQuot A (A ⊓ Subgroup.centralizer (V₂ : Set G)) = n ∧
        E3.mQuot V₂ (V₂ ⊓ Subgroup.centralizer (A : Set G)) = n

@[expose] def FactR2Line : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ : Subgroup G) (n : ℕ)
    (h : Flag24 L V X T V₁ V₂ n), ∀ A : Subgroup G, A ≤ pCoreOf 2 (LOf L V₂ ⊔ T) →
      IsElemAbelian 2 A → autI h.elem A ∈ E3.aSet n (autI h.elem X) →
        (⁅V, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V₂ ∧
            V ⊓ Subgroup.centralizer (A : Set G) = V₂) ∨
          (E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) = n ∧
            E3.mQuot V (V ⊓ Subgroup.centralizer (A : Set G)) = n ∧
            ∃ l ∈ LOf L V₂, ⁅V, conjSubgroup A l⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V₁)

@[expose] def FactR2Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ : Subgroup G) (n : ℕ),
    Flag24 L V X T V₁ V₂ n → ∀ A : Subgroup G, A ≤ pCoreOf 2 (LOf L V₂ ⊔ T) →
      V ≤ ⨆ (B : Subgroup G) (_ : B ≤ A ∧ E3.mQuot A B ≤ 2 * n),
        V ⊓ Subgroup.centralizer (B : Set G)

@[expose] def FactL2Point : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ : Subgroup G) (n : ℕ),
    Flag24 L V X T V₁ V₂ n →
      V₂ ⊓ Subgroup.centralizer (LOf L V₂ : Set G) = V ⊓ Subgroup.centralizer (L : Set G) ∧
      ∀ U S : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ U → U ≤ V₂ →
        (V ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ n →
        QuasithinUnique.IsSylowTwoOf S (LOf L V₂) → S ≤ Subgroup.normalizer (U : Set G) →
          ∃ l ∈ LOf L V₂, U = conjSubgroup V₁ l

@[expose] def FactSp4Root : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ : Subgroup G) (n : ℕ),
    Flag24 L V X T V₁ V₂ n → KindSp4 L V n →
    ∀ W : Subgroup G, W ≤ pCoreOf 2 (LOf L V₂ ⊔ T) →
      E3.mQuot W (W ⊓ Subgroup.centralizer (V : Set G)) = n →
      ¬ V ⊓ Subgroup.centralizer (W : Set G) ≤ V₂ →
        E3.mQuot V (V ⊓ Subgroup.centralizer (W : Set G)) = n ∧
        V ⊓ Subgroup.centralizer (L : Set G) ≤ ⁅V, W⁆

@[expose] def FactSp4NoTransv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ : Subgroup G) (n : ℕ),
    Flag24 L V X T V₁ V₂ n → KindSp4 L V n →
    ∀ A : Subgroup G, A ≤ pCoreOf 2 (LOf L V₂ ⊔ T) →
      E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) = 2 * n →
      (∀ a ∈ A, E3.mQuot V (V ⊓ Subgroup.centralizer ({a} : Set G)) ≠ n) →
        V ⊓ Subgroup.centralizer (L : Set G) ≤ ⁅V, A⁆

structure Facts24 : Prop where
  rootPoint : FactRootPoint
  pointTrans : FactPointTrans
  r2 : FactR2
  r2Line : FactR2Line
  r2Gen : FactR2Gen
  l2Point : FactL2Point
  sp4Root : FactSp4Root
  sp4NoTransv : FactSp4NoTransv

end CFSG.Quasithin.Vol2.Ch11.SecB
