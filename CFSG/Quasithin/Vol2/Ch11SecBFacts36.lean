module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts24

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

structure Flag36 {G : Type} [Group G] (L V W X T V₁ V₂ : Subgroup G) (n : ℕ) : Prop
    extends Flag24 L V X T V₁ V₂ n where
  sl3 : KindSL3 L V n
  cV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥
  elemW : IsElemAbelian 2 W
  le_W : V ≤ W
  L_le_W : L ≤ Subgroup.normalizer (W : Set G)
  T_le_W : T ≤ Subgroup.normalizer (W : Set G)
  two : TwoNaturalSum L W n
  normalizer_le_W : X ⊓ Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (L : Set G)
  odd : ∀ x ∈ X ⊓ Subgroup.normalizer (W : Set G), ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 →
    x ^ p ∈ Subgroup.centralizer (W : Set G) → x ∈ L ⊔ Subgroup.centralizer (W : Set G)

@[expose] def FactVMParam : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V W X T V₁ V₂ : Subgroup G) (n : ℕ)
    (h : Flag36 L V W X T V₁ V₂ n), E3.mParam (autI h.elemW X) = 2 * n

@[expose] def FactVMRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V W X T V₁ V₂ : Subgroup G) (n : ℕ),
    Flag36 L V W X T V₁ V₂ n →
    ∀ E : Subgroup G, E ≤ X ⊓ Subgroup.normalizer (W : Set G) → IsElemAbelian 2 E →
      E3.mQuot E (E ⊓ Subgroup.centralizer (W : Set G)) ≤ 3 * n

@[expose] def FactVMOffender : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V W X T V₁ V₂ : Subgroup G) (n : ℕ)
    (h : Flag36 L V W X T V₁ V₂ n), ∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B →
      autI h.elemW B ∈ E3.aSet (2 * n) (autI h.elemW X) →
        E3.mQuot B (B ⊓ Subgroup.centralizer (W : Set G)) = 2 * n

@[expose] def FactVMR2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V W X T V₁ V₂ : Subgroup G) (n : ℕ)
    (h : Flag36 L V W X T V₁ V₂ n), ∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B →
      autI h.elemW B ∈ E3.aSet (2 * n) (autI h.elemW X) →
      E3.mQuot W (W ⊓ Subgroup.centralizer (B : Set G)) = 2 * n →
        V ⊓ Subgroup.centralizer (B : Set G) = V₂ ∧
        (∀ v ∈ V, v ∉ V₂ → ⁅Subgroup.zpowers v, B⁆ = V₂) ∧
        ∀ A : Subgroup G, A ≤ B →
          IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) ⁅V, A⁆

@[expose] def FactVMRootElt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V W X T V₁ V₂ : Subgroup G) (n : ℕ),
    Flag36 L V W X T V₁ V₂ n →
    ∀ E : Subgroup G, E ≤ X ⊓ Subgroup.normalizer (W : Set G) → IsElemAbelian 2 E →
    ∀ P : Subgroup G, P ≤ W → E3.mQuot P ⊥ = 2 * n →
      (∀ e ∈ E, e ∉ Subgroup.centralizer (W : Set G) → ⁅Subgroup.zpowers e, W⁆ = P) →
        ⁅V, E⁆ = ⊥ ∨
          (⁅V, E⁆ ≤ V ∧ IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) ⁅V, E⁆ ∧
            (V ⊓ Subgroup.centralizer (L : Set G)).relIndex ⁅V, E⁆ = 2 ^ n)

@[expose] def FactVMOddCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V W X T V₁ V₂ : Subgroup G) (n : ℕ),
    Flag36 L V W X T V₁ V₂ n →
    ∀ U : Subgroup G, U ≤ W → E3.mQuot W U = 2 * n →
    ∀ x ∈ X ⊓ Subgroup.normalizer (W : Set G), x ∈ Subgroup.centralizer (U : Set G) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → x ^ p ∈ Subgroup.centralizer (W : Set G) →
      x ∈ Subgroup.centralizer (W : Set G)

@[expose] def FactVMRootInv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V W X T V₁ V₂ : Subgroup G) (n : ℕ),
    Flag36 L V W X T V₁ V₂ n →
    ∀ x ∈ X ⊓ Subgroup.normalizer (W : Set G), x ^ 2 ∈ Subgroup.centralizer (W : Set G) →
      x ∉ Subgroup.centralizer (W : Set G) →
      E3.mQuot W (W ⊓ Subgroup.centralizer ({x} : Set G)) = 2 * n →
        ∃ l ∈ L, conjSubgroup V₁ l ≤ W ⊓ Subgroup.centralizer ({x} : Set G)

@[expose] def FactVMR2Pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V W X T V₁ V₂ : Subgroup G) (n : ℕ),
    Flag36 L V W X T V₁ V₂ n →
    ∀ E : Subgroup G, E ≤ X ⊓ Subgroup.normalizer (W : Set G) → IsElemAbelian 2 E →
      E3.mQuot E (E ⊓ Subgroup.centralizer (W : Set G)) = 2 * n →
      E3.mQuot W (W ⊓ Subgroup.centralizer (E : Set G)) = 2 * n →
        E3.mQuot ⁅W, E⁆ ⊥ = 4 * n ∧
        ∃ a ∈ W, ∃ b ∈ W, a⁻¹ * b ∉ Subgroup.centralizer (E : Set G) ∧
          ⁅Subgroup.zpowers a, E⁆ = ⁅Subgroup.zpowers b, E⁆ ∧ ⁅Subgroup.zpowers a, E⁆ ≠ ⊥

structure FactsVM : Prop where
  param : FactVMParam
  rank : FactVMRank
  offender : FactVMOffender
  r2 : FactVMR2
  rootElt : FactVMRootElt
  oddCent : FactVMOddCent
  rootInv : FactVMRootInv
  r2Pair : FactVMR2Pair

end CFSG.Quasithin.Vol2.Ch11.SecB
