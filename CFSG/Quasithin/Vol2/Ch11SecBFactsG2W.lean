module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts21

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

structure FlagG2 {G : Type} [Group G] (L V X T V₁ V₂ V₃ : Subgroup G) (n : ℕ) : Prop where
  elem : IsElemAbelian 2 V
  two_le : 2 ≤ n
  le_normalizer : L ≤ Subgroup.normalizer (V : Set G)
  commutator_eq : ⁅V, L⁆ = V
  nat : NatModuleOf L V n
  kind : KindG2 L V n
  le_X : L ≤ X
  normalizer_le : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G)
  sylow : QuasithinUnique.IsSylowTwoOf T (L ⊔ T)
  T_le_V : T ≤ Subgroup.normalizer (V : Set G)
  T_le_L : T ≤ Subgroup.normalizer (L : Set G)
  cV_le : V ⊓ Subgroup.centralizer (L : Set G) ≤ V₁
  le₁₂ : V₁ ≤ V₂
  le₂₃ : V₂ ≤ V₃
  le₃ : V₃ ≤ V
  stable₁ : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) V₁
  stable₂ : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) V₂
  stable₃ : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) V₃
  index₁ : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V₁ = 2 ^ n
  index₂ : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V₂ = 2 ^ (n * 2)
  index₃ : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V₃ = 2 ^ (n * 3)
  T_le_V₁ : T ≤ Subgroup.normalizer (V₁ : Set G)
  T_le_V₂ : T ≤ Subgroup.normalizer (V₂ : Set G)
  T_le_V₃ : T ≤ Subgroup.normalizer (V₃ : Set G)

@[expose] def FactG2Offender : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ V₃ : Subgroup G) (n : ℕ)
    (h : FlagG2 L V X T V₁ V₂ V₃ n), V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) → IsElemAbelian 2 A →
      autI h.elem A ∈ E3.aSet (2 * n) (autI h.elem X) →
      ∃ l ∈ L, ∀ x ∈ L, conjSubgroup V₁ l ≤ conjSubgroup V₂ x →
        conjSubgroup V₂ x ≤ conjSubgroup V₃ l →
        ∃ D : Subgroup G, D ≤ A ∧ A ⊓ Subgroup.centralizer (V : Set G) ≤ D ∧
          E3.mQuot A D = 2 * n ∧
          A ⊓ Subgroup.centralizer
            ((V ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) = D ∧
          ⁅V ⊓ Subgroup.centralizer (D : Set G), A⁆ = conjSubgroup V₂ x

@[expose] def FactG2RootLine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ V₃ : Subgroup G) (n : ℕ),
    FlagG2 L V X T V₁ V₂ V₃ n → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    ∀ E : Subgroup G, E ≤ X ⊓ Subgroup.normalizer (V : Set G) → IsElemAbelian 2 E →
      E3.mQuot V (V ⊓ Subgroup.centralizer (E : Set G)) = 2 * n →
        ∃ l ∈ L, ⁅V, E⁆ = conjSubgroup V₂ l

@[expose] def FactG2LineGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ V₃ : Subgroup G) (n : ℕ),
    FlagG2 L V X T V₁ V₂ V₃ n → ∀ l ∈ L,
      L ≤ (⨆ (x : G) (_ : x ∈ L ∧ conjSubgroup V₁ l ≤ conjSubgroup V₂ x ∧
          conjSubgroup V₂ x ≤ conjSubgroup V₃ l), LOf L (conjSubgroup V₂ x)) ⊔
        (L ⊓ Subgroup.centralizer (V : Set G))

structure FactsG2W : Prop where
  offender : FactG2Offender
  rootLine : FactG2RootLine
  lineGen : FactG2LineGen

end CFSG.Quasithin.Vol2.Ch11.SecB
