module

public import CFSG.Quasithin.Vol2.Ch11StatementsA
public import CFSG.Quasithin.Vol2.Ch1Xi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

@[expose] def Obl11_5_7Sp4Y : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → IsVi T L I n 3 V₃ → KindSp4 L (fsuV T I) n →
    ¬ IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) →
    KOf L V₁ V₁ ≠ LOf L V₁ → pCoreOf 2 L = fsuV T I →
    ⁅conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)), KOf L V₁ V₁⁆ ≤
      conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) →
      Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) ≤
        Subgroup.normalizer ((fsuV T I ⊔ conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) :
          Subgroup G) : Set G)

end CFSG.Quasithin.Vol2.Ch11.SecF
