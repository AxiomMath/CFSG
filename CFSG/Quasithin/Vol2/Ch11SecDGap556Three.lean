module

public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Gap11_5_6Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ X H₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → IsCartanX T L X → InH (LOf L V₁ ⊔ T) H₁ →
    ¬ H₁ ≤ Subgroup.normalizer (L : Set G) → H₁ ≤ Subgroup.normalizer (V₁ : Set G) →
      ∀ I' : Subgroup G, quasithinIsCComponent I' (Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) →
        CFSG.IsQuasisimple (↥I' ⧸ CFSG.pCore 2 ↥I') →
        ⁅I', X⁆ ≤ pCoreOf 2 (Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))

end CFSG.Quasithin.Vol2.Ch11.SecD
