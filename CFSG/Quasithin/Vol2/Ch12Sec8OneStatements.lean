module

public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

structure Hyp1281One (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) : Prop where
  hyp : Hyp1223 G T L V
  n_mem : n = 3 ∨ n = 4 ∨ n = 5
  quot : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
  natural : ∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ n 1
  not_linear : ¬ LieModel G .PSL (n + 1) 2 1
  not_alt9 : ¬ Nonempty (G ≃* alternatingGroup (Fin 9))
  not_m24 : ¬ Nonempty (G ≃* NativeSporadic.M24)

@[expose] def IsTSub (T V W : Subgroup G) (i : ℕ) : Prop :=
  W ≤ V ∧ Nat.card W = 2 ^ i ∧ T ≤ Subgroup.normalizer (W : Set G)

@[expose] def li128 (n i : ℕ) (L W : Subgroup G) : Subgroup G :=
  if n = 5 ∧ (i = 2 ∨ i = 3) then
    CFSG.inSubgroup CFSG.perfectResidual (L ⊓ Subgroup.normalizer (W : Set G))
  else oTwoUpper (L ⊓ Subgroup.normalizer (W : Set G))

@[expose] def IsHzOne (T L V₁ H : Subgroup G) : Prop :=
  InH (lOne L V₁ ⊔ T) H ∧ H ≤ Subgroup.normalizer (V₁ : Set G) ∧
    ¬ H ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_8_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Hyp1281One G T L V n →
    (autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V = ⊤ ∧
      autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V =
        autOn L V) ∧
    (∀ (i : ℕ) (W₁ W₂ : Subgroup G), W₁ ≤ V → W₂ ≤ V → Nat.card W₁ = 2 ^ i →
      Nat.card W₂ = 2 ^ i → ∃ l ∈ L, CFSG.conjugate W₁ l = W₂) ∧
    (∀ (i : ℕ) (Vi : Subgroup G), IsTSub T V Vi i → ∀ g : G, Vi ≤ CFSG.conjugate V g →
      ∃ k ∈ Subgroup.normalizer (Vi : Set G), CFSG.conjugate V k = CFSG.conjugate V g) ∧
    ∀ V₁ : Subgroup G, IsTSub T V V₁ 1 →
      ¬ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_8_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Hyp1281One G T L V n →
    ∀ V₁ H : Subgroup G, IsTSub T V V₁ 1 → IsHzOne T L V₁ H →
      AlmostSpecialHyp V V₁ L T H ∧
      (tildeOf V₁ (conjClosure V H) ≤ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) ∧
        IsTwoReducedIn (tildeOf V₁ H) (tildeOf V₁ (conjClosure V H))) ∧
      frattiniOf (conjClosure V H) ≤ V₁ ∧
      centralizerMod V₁ H (conjClosure V H) = pCoreOf 2 H

abbrev u128 (V V₁ : Subgroup G) : Subgroup G :=
  conjClosure V (Subgroup.normalizer (V₁ : Set G))

abbrev zU128 (V V₁ : Subgroup G) : Subgroup G := centerOf (u128 V V₁)

abbrev w128 (V V₁ V₂ : Subgroup G) : Subgroup G :=
  u128 V V₁ ⊓ Subgroup.centralizer (V₂ : Set G)

abbrev p128 (T L V : Subgroup G) : Subgroup G :=
  (L ⊔ T) ⊓ ⨅ (Y : Subgroup G) (_ : ∃ i, 2 ≤ i ∧ IsTSub T V Y i),
    Subgroup.normalizer (Y : Set G)

abbrev i128 (T L V V₁ : Subgroup G) : Subgroup G :=
  conjClosure (u128 V V₁) (p128 T L V)

structure Setting1282One (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ)
    (V₁ V₂ : Subgroup G) : Prop where
  hyp : Hyp1281One G T L V n
  v1 : IsTSub T V V₁ 1
  v2 : IsTSub T V V₂ 2
  le : V₁ ≤ V₂
  nonabelian : ¬ IsMulCommutative ↥(u128 V V₁)

@[expose] def Lemma12_8_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
      ((i128 T L V V₁ = oTwoUpper (p128 T L V) ⊔ u128 V V₁ ∧
          i128 T L V V₁ = u128 V V₁ ⊔ CFSG.conjugate (u128 V V₁) g) ∧
        i128 T L V V₁ ⊓ Subgroup.centralizer (V₂ : Set G) = pCoreOf 2 (i128 T L V V₁) ∧
        Subgroup.normalizer (V₂ : Set G) ≤
          Subgroup.normalizer (oTwoUpper (p128 T L V) : Set G) ∧
        Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (i128 T L V V₁ : Set G)) ∧
      (pCoreOf 2 (i128 T L V V₁) = w128 V V₁ V₂ ⊔ CFSG.conjugate (w128 V V₁ V₂) g ∧
        ⁅w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g, i128 T L V V₁⁆ = V₂ ∧
        Nonempty (↥(i128 T L V V₁) ⧸ CFSG.pCore 2 ↥(i128 T L V V₁) ≃* Equiv.Perm (Fin 3)) ∧
        ∀ y ∈ i128 T L V V₁, orderOf y = 3 → ∀ s ∈ pCoreOf 2 (i128 T L V V₁),
          s * y * s⁻¹ * y⁻¹ ∈ w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g →
            s ∈ w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g) ∧
      (∀ u ∈ u128 V V₁, u ∉ w128 V V₁ V₂ →
        {s ∈ pCoreOf 2 (i128 T L V V₁) |
            s * u * s⁻¹ * u⁻¹ ∈ w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g} =
          (w128 V V₁ V₂ : Set G) ∧
        ⁅pCoreOf 2 (i128 T L V V₁), Subgroup.zpowers u⁆ ⊔
            (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g) = w128 V V₁ V₂ ∧
        ⁅CFSG.conjugate (w128 V V₁ V₂) g, Subgroup.zpowers u⁆ ⊔
            (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g) = w128 V V₁ V₂) ∧
      (∀ y ∈ CFSG.conjugate (w128 V V₁ V₂) g, y ∉ w128 V V₁ V₂ →
        ∀ u ∈ u128 V V₁, u * y * u⁻¹ * y⁻¹ ∈ V₁ → u ∈ w128 V V₁ V₂) ∧
      (CFSG.conjugate (w128 V V₁ V₂) g ⊓
          centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) =
          w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g ∧
        CFSG.conjugate (w128 V V₁ V₂) g ⊓
          centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) =
          w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g) ∧
      (∀ u ∈ u128 V V₁, u ∉ w128 V V₁ V₂ → ∀ x ∈ CFSG.conjugate (w128 V V₁ V₂) g,
        x * u * x⁻¹ * u⁻¹ ∈ zU128 V V₁ →
          x ∈ CFSG.conjugate (zU128 V V₁) g ⊔ (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g)) ∧
      CFSG.conjugate V₁ g ⊓ zU128 V V₁ = ⊥

@[expose] def Lemma12_8_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
      zU128 V V₁ ⊓ CFSG.conjugate (u128 V V₁) g =
          (zU128 V V₁ ⊓ CFSG.conjugate (zU128 V V₁) g) ⊔ V₁ ∧
      zU128 V V₁ ⊓ CFSG.conjugate (zU128 V V₁) g = centerOf (i128 T L V V₁) ∧
      (V₁ < zU128 V V₁ ⊓ CFSG.conjugate (u128 V V₁) g →
        quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁) ≠ ⊥) ∧
      (⁅w128 V V₁ V₂, CFSG.conjugate (zU128 V V₁) g⁆ ≤ zU128 V V₁ ⊔ V₂ ∧
        ∀ x ∈ CFSG.conjugate (zU128 V V₁) g,
          (zU128 V V₁).relIndex (⁅u128 V V₁, Subgroup.zpowers x⁆ ⊔ zU128 V V₁) ≤ 4) ∧
      (CFSG.conjugate (zU128 V V₁) g ≤ u128 V V₁ →
        zU128 V V₁ = centerOf (i128 T L V V₁) ⊔ V₁ ∧ centerOf (i128 T L V V₁) ⊓ V₁ = ⊥ ∧
          ⁅L, centerOf (i128 T L V V₁)⁆ = ⊥) ∧
      (CFSG.conjugate (zU128 V V₁) g ⊓
          centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) =
          CFSG.conjugate (zU128 V V₁) g ⊓
            centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) ∧
        CFSG.conjugate (zU128 V V₁) g ⊓
            centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) =
          CFSG.conjugate (zU128 V V₁) g ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ∧
        CFSG.conjugate (zU128 V V₁) g ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) =
          CFSG.conjugate (zU128 V V₁) g ⊓ u128 V V₁ ∧
        CFSG.conjugate (zU128 V V₁) g ⊓ u128 V V₁ =
          (CFSG.conjugate (zU128 V V₁) g ⊓ zU128 V V₁) ⊔ CFSG.conjugate V₁ g ∧
        (CFSG.conjugate (zU128 V V₁) g ⊓ zU128 V V₁) ⊔ CFSG.conjugate V₁ g =
          centerOf (i128 T L V V₁) ⊔ CFSG.conjugate V₁ g ∧
        centerOf (i128 T L V V₁) ⊔ CFSG.conjugate V₁ g ≤ u128 V V₁)

@[expose] def Lemma12_8_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
      ⁅w128 V V₁ V₂, CFSG.conjugate (w128 V V₁ V₂) g⁆ ≤
          w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g ∧
      IsElemAbelian 2 (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g) ∧
      centralizerMod (zU128 V V₁) (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g)
          (CFSG.conjugate (w128 V V₁ V₂) g) ⊔ zU128 V V₁ = V₂ ⊔ zU128 V V₁

@[expose] def Lemma12_8_12_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
      Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V₂ : Set G) ≤
          Subgroup.normalizer ((CFSG.conjugate (w128 V V₁ V₂) g ⊔
            centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) :
              Subgroup G) : Set G) ∧
      Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V₂ : Set G) ≤
          Subgroup.normalizer ((CFSG.conjugate (zU128 V V₁) g ⊔
            centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) :
              Subgroup G) : Set G)

@[expose] def Lemma12_8_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
      V ≤ w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g ∧
      CFSG.conjugate (zU128 V V₁) g ≤ Subgroup.centralizer (V : Set G) ∧
      (V₁ < zU128 V V₁ → ¬ CFSG.conjugate (zU128 V V₁) g ≤
        centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁)) ∧
      CFSG.Open.pRank 3 (centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂) ≤ 1

end CFSG.Quasithin.H13
