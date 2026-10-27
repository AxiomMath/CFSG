module

public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Background.E6Hyp

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Pointwise

@[expose] def AS_C_1_32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
      IsG2Block L ∨ IsAltBlockType L 6 ∨ IsSp4Block L ∨ IsHatA6Block L ∨
        ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
          Fintype.card F = 2 ^ n ∧ IsModO2Surj L α

@[expose] def AS_C_1_34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α) →
      ∃ i : ℕ, IsC134Case i G₀ R L

@[expose] def AS_A_1_12 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X Y : Subgroup (MulAut V), IsCyclic ↥X →
    (∀ v w : V, v ≠ 1 → w ≠ 1 → ∃! x : ↥X, (x : MulAut V) v = w) →
    X ≤ Y → Odd (Nat.card Y) → Y ≤ Subgroup.normalizer (X : Set (MulAut V))

@[expose] def AS_A_1_28 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
    (∀ P : Subgroup G, P ≠ ⊥ → IsPGroup 2 P → pRank p (Subgroup.normalizer (P : Set G)) ≤ 2) →
    ∀ H : Subgroup G, 2 < pRank p (pCoreOf p H) →
      pRank 2 H ≤ 3 ∧ (pRank 2 H = 3 → ∃ a ∈ H, orderOf a = 2 ∧
        ∀ h ∈ H, a * h * a⁻¹ * h⁻¹ ∈ oddCoreIn H)

@[expose] def AS_G_1_6 : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (Gm R : Subgroup (MulAut U)) (e : ℕ), 1 < e →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ e ∧
      Nonempty (↥Gm ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    IsSylowTwoOf R Gm →
    (⨆ g ∈ Gm, (fixV R).map (g : MulAut U).toMonoidHom) = ⊤ →
    (∀ r ∈ R, r ≠ 1 → fixV (Subgroup.zpowers r) = fixV R) →
      ∃ (s : ℕ) (W : Fin s → Subgroup U), (∀ i, fixV Gm ≤ W i) ∧
        (∀ i, W i ⊓ (fixV Gm ⊔ ⨆ (j : Fin s) (_ : j ≠ i), W j) = fixV Gm) ∧
        (fixV Gm ⊔ ⨆ i, W i) = ⊤ ∧ ∀ i, BinaryNaturalSL Gm (W i) (fixV Gm) 2 e

@[expose] def GammaE64 {G : Type} [Group G] (M V U : Subgroup G) : Prop :=
  U ≠ ⊥ ∧ U ≤ V ∧ ¬ Subgroup.centralizer (U : Set G) ≤ M ∧
    twoPrimeResidual (M ⊓ Subgroup.centralizer (U : Set G)) ≤
      M ⊓ Subgroup.centralizer (V : Set G)

@[expose] def AS_E_6_6_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G), E6.HypE61 T M V → GammaE64 M V U →
    U ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ →
      CharTwo (Subgroup.centralizer (U : Set G))

@[expose] def AS_E_6_7_one : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U K : Subgroup G), E6.HypE61 T M V →
    GammaE64 M V U → T ⊓ Subgroup.centralizer (V : Set G) ≤ K →
    K ≤ Subgroup.centralizer (U : Set G) → CharTwo K →
      ∃ (s : ℕ) (Lb : Fin s → Subgroup G), s ≤ 2 ∧
        (∀ i, IsBlock2 K (Lb i) ∧
          ((∃ n : ℕ, IsLin2Type (Lb i) n) ∨ IsAltType (Lb i) 3 ∨ IsAltType (Lb i) 5) ∧
          Lb i = ⁅Lb i, thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))⁆) ∧
        (∀ i j, i ≠ j → ⁅Lb i, Lb j⁆ = ⊥) ∧
        (K : Set G) = ((K ⊓ M : Subgroup G) : Set G) * ((⨆ i, Lb i : Subgroup G) : Set G)

@[expose] def AS_E_6_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V W M₀ : Subgroup G), E6.HypE61 T M V → W ≠ ⊥ →
    W ≤ V → twoPrimeResidual (M ⊓ Subgroup.centralizer (W : Set G)) ≤
      M ⊓ Subgroup.centralizer (V : Set G) →
    CharTwo (Subgroup.centralizer (W : Set G)) →
    (pRank 3 (Subgroup.centralizer (W : Set G)) ≤ 1 ∨
      ∃ Y : Subgroup G, Y ≤ Subgroup.normalizer (W : Set G) ∧ Nat.card Y = 3 ∧
        Y ⊓ Subgroup.centralizer (W : Set G) = ⊥) →
    T ≤ M₀ → M₀ ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) →
    IsUniqueM M₀ M → IsMaxSubgroupIn M₀ (M₀ ⊓ Subgroup.normalizer (W : Set G)) →
    (M₀ ⊓ Subgroup.normalizer (W : Set G)).relIndex M₀ ≠ 2 →
      Subgroup.centralizer (W : Set G) ≤ M

end CFSG.Quasithin.ASInputs
