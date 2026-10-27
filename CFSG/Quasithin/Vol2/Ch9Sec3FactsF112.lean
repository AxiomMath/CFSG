module

public import CFSG.Quasithin.Vol2.Ch5StatementsDS

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def F112FourLinkFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    F112ListALegacyBare L1 L2 S → IsL2Quot 2 (oTwoQuot ↥L1) → IsL2Quot 2 (oTwoQuot ↥L2) →
    ∀ Li Lj : Subgroup G, ((Li = L1 ∧ Lj = L2) ∨ (Li = L2 ∧ Lj = L1)) →
    ∀ Z₀ : Subgroup G, Z₀ ≠ ⊥ → Z₀ ≤ centerOf S → Z₀ ≤ Subgroup.centralizer (Li : Set G) →
      pCoreOf 2 (Lj ⊔ S) = ⁅pCoreOf 2 (Lj ⊔ S), Lj⁆

@[expose] def F112FourLinkFactC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    F112ListA L1 L2 S → IsL2Quot 2 (oTwoQuot ↥L1) → IsL2Quot 2 (oTwoQuot ↥L2) →
    ∀ Li Lj : Subgroup G, ((Li = L1 ∧ Lj = L2) ∨ (Li = L2 ∧ Lj = L1)) →
    ∀ Z₀ : Subgroup G, Z₀ ≠ ⊥ → Z₀ ≤ centerOf S → Z₀ ≤ Subgroup.centralizer (Li : Set G) →
      pCoreOf 2 (Lj ⊔ S) = ⁅pCoreOf 2 (Lj ⊔ S), Lj⁆

end CFSG.Quasithin.H13.Ch9
