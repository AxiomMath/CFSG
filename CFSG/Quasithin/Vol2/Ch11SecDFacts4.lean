module

public import CFSG.Quasithin.Vol2.Ch11SecDFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def CartanFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ X : Subgroup G),
    NatSetting11 G T L I n → (KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) →
    IsVi T L I n 1 V₁ → IsCartanX T L X →
      X ⊓ Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)) = ⊥ ∧
        ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 →
          ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2

end CFSG.Quasithin.Vol2.Ch11.SecD
