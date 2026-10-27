module

public import CFSG.Quasithin.Background.E6Hyp
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open scoped IsMulCommutative

@[expose] def AS_C_1_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T : Subgroup G), IsSylowTwoOf T (L ⊔ T) →
    T ≤ Subgroup.normalizer (L : Set G) → IsShort2 L →
      (frattini ↥(pCoreOf 2 (L ⊔ T))).map (pCoreOf 2 (L ⊔ T)).subtype ≤
          T ⊓ Subgroup.centralizer (L : Set G) ∧
      (∀ m : ℕ, (m = 3 ∨ m = 5) → IsAltType L m →
        pCoreOf 2 (L ⊔ T) = blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
        blockU L ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
        (∃ _ : IsMulCommutative ↥(blockU L),
          AlternatingNatural (V := ↥(blockU L)) (autOn L (blockU L)) ⊤ ⊥ m) ∧
        (m = 3 → Nonempty (↥L ≃* alternatingGroup (Fin 4))) ∧
        (m = 5 → ∃ _ : ((blockU L).subgroupOf L).Normal,
          Nonempty (↥L ⧸ (blockU L).subgroupOf L ≃* alternatingGroup (Fin 5)) ∨
            (Nonempty (↥L ⧸ (blockU L).subgroupOf L ≃*
                Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
              Nat.card (Subgroup.center ↥L) = 2)) ∧
        pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (pCoreOf 2 L : Set G)) ∧
      (IsAltBlockType L 6 → pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (pCoreOf 2 L : Set G))

@[expose] def AS_E_3_39 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V M : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    E3.HypE336 T V M → (E3.nPrime (autI hV ⊤) : ℕ∞) < E3.rParam V →
    ∀ H : Subgroup G, IsHStar T M H →
      (E3.wParam T V ≤ E1.nParam H ∧ E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞)) ∧
      (E3.aParam (autI hV ⊤) < E3.sParam hV →
        0 < E3.sParam hV - E3.aParam (autI hV ⊤) ∧
          ((E3.sParam hV - E3.aParam (autI hV ⊤) : ℕ) : ℕ∞) ≤ E3.wParam T V)

@[expose] def AS_E_6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G) (hV : IsElemAbelian 2 V),
    E6.HypE61 T M V → 2 < E3.mParam (autI hV M) →
      (E3.mParam (autI hV M) : ℕ∞) ≤ E3.rParam V ∧ E3.sParam hV = E3.mParam (autI hV M)

@[expose] def AS_E_6_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G), E6.HypE61 T M V → U ≠ ⊥ → U ≤ V →
    M ⊓ Subgroup.centralizer (U : Set G) = M ⊓ Subgroup.centralizer (V : Set G) →
    ¬ Subgroup.centralizer (U : Set G) ≤ M →
      (∃ U₁ : Subgroup G, U ≤ U₁ ∧ U₁ ≤ V ∧ E3.mQuot V U₁ = 1 ∧
        ¬ Subgroup.centralizer (U₁ : Set G) ≤ M) ∧ E3.rParam V = 1

end CFSG.Quasithin.ASInputs
