module

public import CFSG.Quasithin.Background.C2Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def KG1468TwoRu : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), CFSG.IsQuasisimple ↥Y →
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* NativeSporadic.Carrier .Ru) →
    ∀ z ∈ Y, orderOf z = 2 → z ∉ Subgroup.centralizer (Y : Set G) →
    Nonempty (↥(oTwoUpper (Y ⊓ Subgroup.centralizer ({z} : Set G))) ⧸
        CFSG.pCore 2 ↥(oTwoUpper (Y ⊓ Subgroup.centralizer ({z} : Set G))) ≃*
          alternatingGroup (Fin 5)) →
    ∀ E : Subgroup G, E ≤ pCoreOf 2 (oTwoUpper (Y ⊓ Subgroup.centralizer ({z} : Set G))) →
      IsElemAbelian 2 E → Nat.card E = 8 → z ∈ E → E ⊓ Subgroup.centralizer (Y : Set G) = ⊥ →
      (∀ e ∈ E, ∀ w ∈ pCoreOf 2 (oTwoUpper (Y ⊓ Subgroup.centralizer ({z} : Set G))),
        e * w * e⁻¹ * w⁻¹ ∈ Subgroup.zpowers z) →
      (∃ y ∈ oTwoUpper (Y ⊓ Subgroup.centralizer ({z} : Set G)), orderOf y = 3 ∧
        y ∈ Subgroup.normalizer (E : Set G) ∧
        ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers z → e ∈ Subgroup.zpowers z) →
      (∃ S : Subgroup G, IsSylowTwoOf S Y ∧ S ≤ Subgroup.normalizer (E : Set G) ∧
        S ≤ Subgroup.centralizer ({z} : Set G)) →
      Nonempty (↥(oTwoUpper (Y ⊓ Subgroup.normalizer (E : Set G))) ⧸
          CFSG.pCore 2 ↥(oTwoUpper (Y ⊓ Subgroup.normalizer (E : Set G))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))

@[expose] def KG1468Blocks : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y R M I : Subgroup G), HypC23 Y R M → I ∈ cComp Y →
    (I.subgroupOf Y).Normal → CharTwo I → CFSG.IsQuasisimple (↥I ⧸ CFSG.pCore 2 ↥I) →
    ¬ I ≤ M → R ≤ Subgroup.normalizer (I : Set G) →
    Nonempty (↥(oTwoUpper (I ⊓ M)) ⧸ CFSG.pCore 2 ↥(oTwoUpper (I ⊓ M)) ≃*
      alternatingGroup (Fin 5)) →
    ⁅pCoreOf 2 (oTwoUpper (I ⊓ M)), oTwoUpper (I ⊓ M)⁆ ≤
        Subgroup.centralizer (pCoreOf 2 (oTwoUpper (I ⊓ M)) : Set G) ∨
      ∃ y ∈ I, orderOf y = 3 ∧ y ∈ Subgroup.normalizer (oTwoUpper (I ⊓ M) : Set G) ∧
        ∀ b ∈ oTwoUpper (I ⊓ M), y * b * y⁻¹ * b⁻¹ ∈ pCoreOf 2 (oTwoUpper (I ⊓ M))

end CFSG.Quasithin.H13
